/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FileHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/System/Time.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/system_error.h"
#endif

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>

#include <cerrno>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>
#include <iostream>

#include <mpi.h>

using namespace llvm;
using namespace klee;

#define START_PREFIX_TASK 0
#define KILL 1
#define FINISH 2
#define OFFLOAD 3
#define OFFLOAD_RESP 4
#define BUG_FOUND 5
#define TIMEOUT 6
#define NORMAL_TASK 7
#define KILL_COMP 8
#define READY_TO_OFFLOAD 9
#define NOT_READY_TO_OFFLOAD 10

#define PREFIX_MODE 101
#define NO_MODE 103

#define ENABLE_CLEANUP false
#define MASTER_NODE 0
#define FLUSH true

enum searchMode{
  DFS,
  BFS,
  RAND,
  COVNEW
};

namespace klee {
  extern RNG theRNG;
}

namespace {
  cl::opt<std::string>
  InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

  cl::opt<std::string>
  ErrorLocation("error-location",
        cl::desc("locations a failure is expected (e.g. <file1>[:line],<file2>[:line],..)"),
        cl::init("none"));

  cl::opt<std::string>
  errorFile("error-file",
        cl::desc("name of the file where error is exepected"),
        cl::init("none"));

  cl::opt<std::string>
  EntryPoint("entry-point",
               cl::desc("Consider the function with the given name as the entrypoint"),
               cl::init("main"));

  cl::opt<std::string>
  RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));

  cl::opt<std::string>
  Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter,
            cl::desc("<program arguments>..."));

  cl::opt<bool>
  NoOutput("no-output",
           cl::desc("Don't generate test files"));

  cl::opt<bool>
  WarnAllExternals("warn-all-externals",
                   cl::desc("Give initial warning for all externals."));

  cl::opt<bool>
  WriteCVCs("write-cvcs",
            cl::desc("Write .cvc files for each test case"));

  cl::opt<bool>
  WriteKQueries("write-kqueries",
            cl::desc("Write .kquery files for each test case"));

  cl::opt<bool>
  WriteSMT2s("write-smt2s",
            cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));

  cl::opt<bool>
  WriteCov("write-cov",
           cl::desc("Write coverage information for each test case"));

  cl::opt<bool>
  WriteTestInfo("write-test-info",
                cl::desc("Write additional test case information"));

  cl::opt<bool>
  WritePaths("write-paths",
                cl::desc("Write .path files for each test case"));

  cl::opt<bool>
  WriteSymPaths("write-sym-paths",
                cl::desc("Write .sym.path files for each test case"));

  cl::opt<bool>
  OptExitOnError("exit-on-error",
              cl::desc("Exit if errors occur"));

  cl::opt<unsigned int>
  timeOut("timeOut",
          cl::desc("Exit on timeout"),
          cl::init(0)); 

	/*** Linking options ***/

 	cl::OptionCategory LinkCat("Linking options",
                            "These options control the libraries being linked.");

  enum class LibcType {
    FreeStandingLibc, KleeLibc, UcLibc 
  };
	
	cl::opt<LibcType>
	Libc("libc",
     cl::desc("Choose libc version (none by default)."),
     cl::values(
                clEnumValN(LibcType::FreeStandingLibc,
                           "none",
                           "Don'tlinkinalibc(onlyprovide freestanding environment)"),
                clEnumValN(LibcType::KleeLibc,
                           "klee",
                           "Link in KLEE's libc"),
                clEnumValN(LibcType::UcLibc, "uclibc",
                           "Link in uclibc (adapted for KLEE)")
                KLEE_LLVM_CL_VAL_END),
     cl::init(LibcType::FreeStandingLibc),
     cl::cat(LinkCat));
	

  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
		cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
		cl::init(false));

  cl::opt<bool>
  OptimizeModule("optimize",
                 cl::desc("Optimize before execution"),
		 cl::init(false));

  cl::opt<bool>
  CheckDivZero("check-div-zero",
               cl::desc("Inject checks for division-by-zero"),
               cl::init(true));

  cl::opt<bool>
  CheckOvershift("check-overshift",
               cl::desc("Inject checks for overshift"),
               cl::init(true));

  cl::opt<std::string>
  OutputDir("output-dir",
            cl::desc("Directory to write results in (defaults to klee-out-N)"),
            cl::init(""));

  cl::opt<bool>
  ReplayKeepSymbolic("replay-keep-symbolic",
                     cl::desc("Replay the test cases only by asserting "
                              "the bytes, not necessarily making them concrete."));

  cl::list<std::string>
      ReplayKTestFile("replay-ktest-file",
                      cl::desc("Specify a ktest file to use for replay"),
                      cl::value_desc("ktest file"));

  cl::list<std::string>
      ReplayKTestDir("replay-ktest-dir",
                   cl::desc("Specify a directory to replay ktest files from"),
                   cl::value_desc("output directory"));

  cl::opt<std::string>
  ReplayPathFile("replay-path",
                 cl::desc("Specify a path file to replay"),
                 cl::value_desc("path file"));

  cl::opt<unsigned int>
  phase1Depth("phase1Depth",
                 cl::desc("Depth to limit the exploration upto"),
                 cl::init(0));

  cl::opt<unsigned int>
  phase2Depth("phase2Depth",
                 cl::desc("Depth to limit the exploration upto"),
                 cl::init(0));

  cl::opt<std::string>
  rangeBounds("rangeBounds",
                 cl::desc("upperlowerbounds"),
                 cl::value_desc("a bit vector of branch histories"),
                 cl::init("0"));

  cl::opt<std::string>
  pathFile("pathFile",
                 cl::desc("path file name"),
                 cl::value_desc("path file"),
                 cl::init("pathFile"));

  cl::opt<std::string>
  searchPolicy("searchPolicy",
                 cl::desc("policy name"),
                 cl::value_desc("policy name"),
                 cl::init("DFS"));

	cl::opt<std::string>
	Mode("mode",
		  cl::desc("offload using tests or prefixes"),
			cl::value_desc("same"),
			cl::init("test"));

  cl::list<std::string>
  SeedOutFile("seed-out");

  cl::list<std::string>
  SeedOutDir("seed-out-dir");

  cl::list<std::string>
  LinkLibraries("link-llvm-lib",
		cl::desc("Link the given libraries before execution"),
		cl::value_desc("library file"));

  cl::opt<unsigned>
  MakeConcreteSymbolic("make-concrete-symbolic",
                       cl::desc("Probabilistic rate at which to make concrete reads symbolic, "
				"i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  "
				"Used for testing."),
                       cl::init(0));

  cl::opt<unsigned>
  StopAfterNTests("stop-after-n-tests",
	     cl::desc("Stop execution after generating the given number of tests."
         "Extra tests corresponding to partially explored paths will also be dumped."),
	     cl::init(0));

  cl::opt<bool>
  Watchdog("watchdog",
           cl::desc("Use a watchdog process to enforce --max-time."),
           cl::init(0));

  cl::opt<bool>
  lb("lb",
      cl::desc("load balance"),
      cl::init(false));
}

extern cl::opt<std::string> MaxTime;

/***/

class KleeHandler : public InterpreterHandler {
private:
  Interpreter *m_interpreter;
  TreeStreamWriter *m_pathWriter, *m_symPathWriter;
	std::unique_ptr<llvm::raw_ostream> m_infoFile;

  SmallString<128> m_outputDirectory;

  std::string outputFileName;

  unsigned m_numTotalTests;     // Number of tests received from the interpreter
  unsigned m_numGeneratedTests; // Number of tests successfully generated
  unsigned m_pathsExplored; // number of paths explored so far

  // used for writing .ktest files
  int m_argc;
  char **m_argv;

public:
  KleeHandler(int argc, char **argv);
  ~KleeHandler();

  llvm::raw_ostream &getInfoStream() const { return *m_infoFile; }
  /// Returns the number of test cases successfully generated so far
  unsigned getNumTestCases() { return m_numGeneratedTests; }
  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() { m_pathsExplored++; }
  void resetPathsExplored() { m_pathsExplored=0; } 

  void setInterpreter(Interpreter *i);

  std::string getOutputDir();

  unsigned processTestCase(const ExecutionState  &state,
                       const char *errorMessage,
                       const char *errorSuffix,
                       bool writeOutput);

  std::string getOutputFilename(const std::string &filename);
  std::unique_ptr<llvm::raw_fd_ostream> openOutputFile(const std::string &filename);
  std::string getTestFilename(const std::string &suffix, unsigned id);
  std::unique_ptr<llvm::raw_fd_ostream> openTestFile(const std::string &suffix, unsigned id);

  // load a .path file
  static void loadPathFile(std::string name,
                           std::vector<bool> &buffer);

  static void getKTestFilesInDir(std::string directoryPath,
                                 std::vector<std::string> &results);

  static std::string getRunTimeLibraryPath(const char *argv0);
};

KleeHandler::KleeHandler(int argc, char **argv)
    : m_interpreter(0), m_pathWriter(0), m_symPathWriter(0),
      m_outputDirectory(), m_numTotalTests(0), m_numGeneratedTests(0),
      m_pathsExplored(0), m_argc(argc), m_argv(argv) {

  // create output directory (OutputDir or "klee-out-<i>")
  bool dir_given = OutputDir != "";
  SmallString<128> directory(dir_given ? OutputDir : InputFile);

  if (!dir_given) sys::path::remove_filename(directory);
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
  if ((ec = sys::fs::make_absolute(directory)) != errc::success) {
#else
  if (auto ec = sys::fs::make_absolute(directory)) {
#endif
    klee_error("unable to determine absolute path: %s", ec.message().c_str());
  }

  //if (dir_given) {
    // OutputDir
  //  if (mkdir(directory.c_str(), 0775) < 0)
  //   klee_error("cannot create \"%s\": %s", directory.c_str(), strerror(errno));
  //  m_outputDirectory = directory;
  //}
  if(!dir_given) {
     klee_error("Output Directory not Provided");
  } 
  else {
    // "klee-out-<i>"
		int i = 0;
    for (; i <= INT_MAX; ++i) {
      SmallString<128> d(directory);
      //llvm::sys::path::append(d, "klee-out-");
      raw_svector_ostream ds(d); ds << i; ds.flush();

      // create directory and try to link klee-last
      if (mkdir(d.c_str(), 0775) == 0) {
        m_outputDirectory = d;
        outputFileName = OutputDir+std::to_string(i);
        int world_rank;
        MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);
        std::cout<<"Output Directory World Rank: "<<world_rank<<" Index: " 
                 <<outputFileName<<"\n";

        SmallString<128> klee_last(directory);
        llvm::sys::path::append(klee_last, "klee-last");

        if (((unlink(klee_last.c_str()) < 0) && (errno != ENOENT)) ||
            symlink(m_outputDirectory.c_str(), klee_last.c_str()) < 0) {

          klee_warning("cannot create klee-last symlink: %s", strerror(errno));
        }
        break;
      }

  	  // otherwise try again or exit on error
  	  if (errno != EEXIST)
    	  klee_error("cannot create \"%s\": %s", m_outputDirectory.c_str(), strerror(errno));
		}
		if (i == INT_MAX && m_outputDirectory.str().equals(""))
    	klee_error("cannot create output directory: index out of range");

  }
  klee_message("output directory is \"%s\"", m_outputDirectory.c_str());

  // open warnings.txt
  std::string file_path = getOutputFilename("warnings.txt");
  if ((klee_warning_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open messages.txt
  file_path = getOutputFilename("messages.txt");
  if ((klee_message_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open info
  m_infoFile = openOutputFile("info");
}

std::string KleeHandler::getOutputDir() {
    return outputFileName;
}

KleeHandler::~KleeHandler() {
  delete m_pathWriter;
  delete m_symPathWriter;
  fclose(klee_warning_file);
  fclose(klee_message_file);
  //delete m_infoFile;
}

void KleeHandler::setInterpreter(Interpreter *i) {
  m_interpreter = i;

  if (WritePaths) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    m_interpreter->setPathWriter(m_pathWriter);
  }

  if (WriteSymPaths) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string KleeHandler::getOutputFilename(const std::string &filename) {
  SmallString<128> path = m_outputDirectory;
  sys::path::append(path,filename);
  return path.str();
}

std::unique_ptr<llvm::raw_fd_ostream>
KleeHandler::openOutputFile(const std::string &filename) {
  std::string Error;
  std::string path = getOutputFilename(filename);
  auto f = klee_open_output_file(path, Error);
  if (!f) {
    klee_warning("error opening file \"%s\".  KLEE may have run out of file "
                 "descriptors: try to increase the maximum number of open file "
                 "descriptors by using ulimit (%s).",
                 path.c_str(), Error.c_str());
    return nullptr;
  }
  return f;
}

std::string KleeHandler::getTestFilename(const std::string &suffix, unsigned id) {
  std::stringstream filename;
  filename << "test" << std::setfill('0') << std::setw(6) << id << '.' << suffix;
  return filename.str();
}

std::unique_ptr<llvm::raw_fd_ostream>
KleeHandler::openTestFile(const std::string &suffix,
                                                unsigned id) {
  return openOutputFile(getTestFilename(suffix, id));
}


/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
unsigned KleeHandler::processTestCase(const ExecutionState &state,
                                  const char *errorMessage,
                                  const char *errorSuffix,
                                  bool writeOutput) {
  if (!NoOutput && writeOutput) {
    std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
    bool success = m_interpreter->getSymbolicSolution(state, out);

    if (!success)
      klee_warning("unable to get symbolic solution, losing test case");

    const auto start_time = time::getWallTime();
    unsigned id = ++m_numTotalTests;

    if (success) {
      KTest b;
      b.numArgs = m_argc;
      b.args = m_argv;
      b.symArgvs = 0;
      b.symArgvLen = 0;
      b.numObjects = out.size();
      b.objects = new KTestObject[b.numObjects];
      assert(b.objects);
      for (unsigned i=0; i<b.numObjects; i++) {
        KTestObject *o = &b.objects[i];
        o->name = const_cast<char*>(out[i].first.c_str());
        o->numBytes = out[i].second.size();
        o->bytes = new unsigned char[o->numBytes];
        assert(o->bytes);
        std::copy(out[i].second.begin(), out[i].second.end(), o->bytes);
      }
      if (!kTest_toFile(&b, getOutputFilename(getTestFilename("ktest", id)).c_str())) {
        klee_warning("unable to write output test case, losing it");
      } else {
        ++m_numGeneratedTests;
      }

      for (unsigned i=0; i<b.numObjects; i++)
        delete[] b.objects[i].bytes;
      delete[] b.objects;
    }

    if (errorMessage) {
      auto f = openTestFile(errorSuffix, id);
      if (f)
        *f << errorMessage;
    }

    if (m_pathWriter) {
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(m_interpreter->getPathStreamID(state),
                                   concreteBranches);
      auto f = openTestFile("path", id);
      if (f) {
        for (const auto &branch : concreteBranches) {
          *f << branch << '\n';
        }
      }
    }

    if (errorMessage || WriteKQueries) {
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
      auto f = openTestFile("kquery", id);
      if(f)
        *f << constraints;
    }

    if (WriteCVCs) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
      auto f = openTestFile("cvc", id);
      if(f)
        *f << constraints;
    }

    if(WriteSMT2s) {
      std::string constraints;
        m_interpreter->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
        auto f = openTestFile("smt2", id);
        if(f)
          *f << constraints;
    }

    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(m_interpreter->getSymbolicPathStreamID(state),
                                  symbolicBranches);
      auto f = openTestFile("sym.path", id);
      if (f) {
        for (const auto &branch : symbolicBranches) {
          *f << branch << '\n';
        }
      }
    }

    if (WriteCov) {
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      auto f = openTestFile("cov", id);
      if (f) {
          for (const auto &entry : cov) {
                for (const auto &line : entry.second) {
                        *f << *entry.first << ':' << line << '\n';
                            }
                  }
      }
    }

    if (m_numGeneratedTests == StopAfterNTests)
      m_interpreter->setHaltExecution(true);

    if (WriteTestInfo) {
      //double elapsed_time = util::getWallTime() - start_time;
      time::Span elapsed_time(time::getWallTime() - start_time);
      auto f = openTestFile("info", id);
      *f << "Time to generate test case: "
         << elapsed_time << "s\n";
    }

    return id;
  }
  
  if (errorMessage && OptExitOnError) {
    m_interpreter->prepareForEarlyExit();
    klee_error("EXITING ON ERROR:\n%s\n", errorMessage);
  }

  return 0;
}

  // load a .path file
void KleeHandler::loadPathFile(std::string name,
                                     std::vector<bool> &buffer) {
  std::ifstream f(name.c_str(), std::ios::in | std::ios::binary);

  if (!f.good())
    assert(0 && "unable to open path file");

  while (f.good()) {
    unsigned value;
    f >> value;
    buffer.push_back(!!value);
    f.get();
  }
}

void KleeHandler::getKTestFilesInDir(std::string directoryPath,
                                     std::vector<std::string> &results) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
#else
  std::error_code ec;
#endif
  for (llvm::sys::fs::directory_iterator i(directoryPath, ec), e; i != e && !ec;
       i.increment(ec)) {
    std::string f = (*i).path();
    if (f.substr(f.size()-6,f.size()) == ".ktest") {
          results.push_back(f);
    }
  }

  if (ec) {
    llvm::errs() << "ERROR: unable to read output directory: " << directoryPath
                 << ": " << ec.message() << "\n";
    exit(1);
  }
}

std::string KleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env)
    return std::string(env);

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(
      llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)
      );

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  }
  else
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                       libDir.c_str() << "\n");
  return libDir.str();
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static std::string strip(std::string &in) {
  unsigned len = in.size();
  unsigned lead = 0, trail = len;
  while (lead<len && isspace(in[lead]))
    ++lead;
  while (trail>lead && isspace(in[trail-1]))
    --trail;
  return in.substr(lead, trail-lead);
}

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  // This version always reads response files
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

static void
preparePOSIX(std::vector<std::unique_ptr<llvm::Module>> &loadedModules,
             llvm::StringRef libCPrefix) {
  // Get the main function from the main module and rename it such that it can
  // be called after the POSIX setup
  Function *mainFn = nullptr;
  for (auto &module : loadedModules) {
    mainFn = module->getFunction(EntryPoint);
    if (mainFn)
      break;
  }

  if (!mainFn)
    klee_error("Entry function '%s' not found in module.", EntryPoint.c_str());
  mainFn->setName("__klee_posix_wrapped_main");

  // Add a definition of the entry function if needed. This is the case if we
  // link against a libc implementation. Preparing for libc linking (i.e.
  // linking with uClibc will expect a main function and rename it to
  // _user_main. We just provide the definition here.
  if (!libCPrefix.empty())
    mainFn->getParent()->getOrInsertFunction(EntryPoint,
                                             mainFn->getFunctionType());

  llvm::Function *wrapper = nullptr;
  for (auto &module : loadedModules) {
    wrapper = module->getFunction("__klee_posix_wrapper");
    if (wrapper)
      break;
  }
  assert(wrapper && "klee_posix_wrapper not found");

  // Rename the POSIX wrapper to prefixed entrypoint, e.g. _user_main as uClibc
  // would expect it or main otherwise
  wrapper->setName(libCPrefix + EntryPoint);
}

// This is a terrible hack until we get some real modeling of the
// system. All we do is check the undefined symbols and warn about
// any "unrecognized" externals and about any obviously unsafe ones.

// Symbols we explicitly support
static const char *modelledExternals[] = {
  "_ZTVN10__cxxabiv117__class_type_infoE",
  "_ZTVN10__cxxabiv120__si_class_type_infoE",
  "_ZTVN10__cxxabiv121__vmi_class_type_infoE",

  // special functions
  "_assert",
  "__assert_fail",
  "__assert_rtn",
  "__errno_location",
  "__error",
  "calloc",
  "_exit",
  "exit",
  "free",
  "abort",
  "klee_abort",
  "klee_assume",
  "klee_check_memory_access",
  "klee_define_fixed_object",
  "klee_get_errno",
  "klee_get_valuef",
  "klee_get_valued",
  "klee_get_valuel",
  "klee_get_valuell",
  "klee_get_value_i32",
  "klee_get_value_i64",
  "klee_get_obj_size",
  "klee_is_symbolic",
  "klee_make_symbolic",
  "klee_mark_global",
  "klee_open_merge",
  "klee_close_merge",
  "klee_prefer_cex",
  "klee_posix_prefer_cex",
  "klee_print_expr",
  "klee_print_range",
  "klee_report_error",
  "klee_set_forking",
  "klee_silent_exit",
  "klee_warning",
  "klee_warning_once",
  "klee_alias_function",
  "klee_stack_trace",
  "llvm.dbg.declare",
  "llvm.dbg.value",
  "llvm.va_start",
  "llvm.va_end",
  "malloc",
  "realloc",
  "_ZdaPv",
  "_ZdlPv",
  "_Znaj",
  "_Znwj",
  "_Znam",
  "_Znwm",
  "__ubsan_handle_add_overflow",
  "__ubsan_handle_sub_overflow",
  "__ubsan_handle_mul_overflow",
  "__ubsan_handle_divrem_overflow",
};
// Symbols we aren't going to warn about
static const char *dontCareExternals[] = {
#if 0
  // stdio
  "fprintf",
  "fflush",
  "fopen",
  "fclose",
  "fputs_unlocked",
  "putchar_unlocked",
  "vfprintf",
  "fwrite",
  "puts",
  "printf",
  "stdin",
  "stdout",
  "stderr",
  "_stdio_term",
  "__errno_location",
  "fstat",
#endif

  // static information, pretty ok to return
  "getegid",
  "geteuid",
  "getgid",
  "getuid",
  "getpid",
  "gethostname",
  "getpgrp",
  "getppid",
  "getpagesize",
  "getpriority",
  "getgroups",
  "getdtablesize",
  "getrlimit",
  "getrlimit64",
  "getcwd",
  "getwd",
  "gettimeofday",
  "uname",

  // fp stuff we just don't worry about yet
  "frexp",
  "ldexp",
  "__isnan",
  "__signbit",
};
// Extra symbols we aren't going to warn about with klee-libc
static const char *dontCareKlee[] = {
  "__ctype_b_loc",
  "__ctype_get_mb_cur_max",

  // io system calls
  "open",
  "write",
  "read",
  "close",
};
// Extra symbols we aren't going to warn about with uclibc
static const char *dontCareUclibc[] = {
  "__dso_handle",

  // Don't warn about these since we explicitly commented them out of
  // uclibc.
  "printf",
  "vprintf"
};
// Symbols we consider unsafe
static const char *unsafeExternals[] = {
  "fork", // oh lord
  "exec", // heaven help us
  "error", // calls _exit
  "raise", // yeah
  "kill", // mmmhmmm
};
#define NELEMS(array) (sizeof(array)/sizeof(array[0]))

void externalsAndGlobalsCheck(const llvm::Module *m) {
  std::map<std::string, bool> externals;
  std::set<std::string> modelled(modelledExternals,
                                 modelledExternals+NELEMS(modelledExternals));
  std::set<std::string> dontCare(dontCareExternals,
                                 dontCareExternals+NELEMS(dontCareExternals));
  std::set<std::string> unsafe(unsafeExternals,
                               unsafeExternals+NELEMS(unsafeExternals));

  switch (Libc) {
  case LibcType::KleeLibc:
    dontCare.insert(dontCareKlee, dontCareKlee+NELEMS(dontCareKlee));
    break;
  case LibcType::UcLibc:
    dontCare.insert(dontCareUclibc,
                    dontCareUclibc+NELEMS(dontCareUclibc));
    break;
  case LibcType::FreeStandingLibc: /* silence compiler warning */
    break;
  }

  if (WithPOSIXRuntime)
    dontCare.insert("syscall");

  for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end();
       fnIt != fn_ie; ++fnIt) {
    if (fnIt->isDeclaration() && !fnIt->use_empty())
      externals.insert(std::make_pair(fnIt->getName(), false));
    for (Function::const_iterator bbIt = fnIt->begin(), bb_ie = fnIt->end();
         bbIt != bb_ie; ++bbIt) {
      for (BasicBlock::const_iterator it = bbIt->begin(), ie = bbIt->end();
           it != ie; ++it) {
        if (const CallInst *ci = dyn_cast<CallInst>(it)) {
          if (isa<InlineAsm>(ci->getCalledValue())) {
            klee_warning_once(&*fnIt,
                              "function \"%s\" has inline asm",
                              fnIt->getName().data());
          }
        }
      }
    }
  }
  for (Module::const_global_iterator
         it = m->global_begin(), ie = m->global_end();
       it != ie; ++it)
    if (it->isDeclaration() && !it->use_empty())
      externals.insert(std::make_pair(it->getName(), true));
  // and remove aliases (they define the symbol after global
  // initialization)
  for (Module::const_alias_iterator
         it = m->alias_begin(), ie = m->alias_end();
       it != ie; ++it) {
    std::map<std::string, bool>::iterator it2 =
      externals.find(it->getName());
    if (it2!=externals.end())
      externals.erase(it2);
  }

  std::map<std::string, bool> foundUnsafe;
  for (std::map<std::string, bool>::iterator
         it = externals.begin(), ie = externals.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    if (!modelled.count(ext) && (WarnAllExternals ||
                                 !dontCare.count(ext))) {
      if (unsafe.count(ext)) {
        foundUnsafe.insert(*it);
      } else {
        klee_warning("undefined reference to %s: %s",
                     it->second ? "variable" : "function",
                     ext.c_str());
      }
    }
  }

  for (std::map<std::string, bool>::iterator
         it = foundUnsafe.begin(), ie = foundUnsafe.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    klee_warning("undefined reference to %s: %s (UNSAFE)!",
                 it->second ? "variable" : "function",
                 ext.c_str());
  }
}

static Interpreter *theInterpreter = 0;

static bool interrupted = false;

// Pulled out so it can be easily called from a debugger.
extern "C"
void halt_execution() {
  theInterpreter->setHaltExecution(true);
}

extern "C"
void stop_forking() {
  theInterpreter->setInhibitForking(true);
}

static void interrupt_handle() {
  if (!interrupted && theInterpreter) {
    llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
    halt_execution();
    sys::SetInterruptFunction(interrupt_handle);
  } else {
    llvm::errs() << "KLEE: ctrl-c detected, exiting.\n";
    exit(1);
  }
  interrupted = true;
}

static void interrupt_handle_watchdog() {
  // just wait for the child to finish
}

// This is a temporary hack. If the running process has access to
// externals then it can disable interrupts, which screws up the
// normal "nice" watchdog termination process. We try to request the
// interpreter to halt using this mechanism as a last resort to save
// the state data before going ahead and killing it.
static void halt_via_gdb(int pid) {
  char buffer[256];
  sprintf(buffer,
          "gdb --batch --eval-command=\"p halt_execution()\" "
          "--eval-command=detach --pid=%d &> /dev/null",
          pid);
  //  fprintf(stderr, "KLEE: WATCHDOG: running: %s\n", buffer);
  if (system(buffer)==-1)
    perror("system");
}

// returns the end of the string put in buf
static char *format_tdiff(char *buf, long seconds)
{
  assert(seconds >= 0);

  long minutes = seconds / 60;  seconds %= 60;
  long hours   = minutes / 60;  minutes %= 60;
  long days    = hours   / 24;  hours   %= 24;

  buf = strrchr(buf, '\0');
  if (days > 0) buf += sprintf(buf, "%ld days, ", days);
  buf += sprintf(buf, "%02ld:%02ld:%02ld", hours, minutes, seconds);
  return buf;
}

#ifndef SUPPORT_KLEE_UCLIBC
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module,
		const char *old_name, const char *new_name)
{
  Function *f, *f2;
  f = module->getFunction(new_name);
  f2 = module->getFunction(old_name);
  if (f2) {
    if (f) {
      f2->replaceAllUsesWith(f);
      f2->eraseFromParent();
    } else {
      f2->setName(new_name);
      assert(f2->getName() == new_name);
    }
  }
}

static void
createLibCWrapper(std::vector<std::unique_ptr<llvm::Module>> &modules,
                  llvm::StringRef intendedFunction,
                  llvm::StringRef libcMainFunction) {
  // XXX we need to rearchitect so this can also be used with
  // programs externally linked with libc implementation.

  // We now need to swap things so that libcMainFunction is the entry
  // point, in such a way that the arguments are passed to
  // libcMainFunction correctly. We do this by renaming the user main
  // and generating a stub function to call intendedFunction. There is
  // also an implicit cooperation in that runFunctionAsMain sets up
  // the environment arguments to what a libc expects (following
  // argv), since it does not explicitly take an envp argument.
  auto &ctx = modules[0]->getContext();
  Function *userMainFn = modules[0]->getFunction(intendedFunction);
  assert(userMainFn && "unable to get user main");
  // Rename entry point using a prefix
  userMainFn->setName("__user_" + intendedFunction);

  // force import of libcMainFunction
  llvm::Function *libcMainFn = nullptr;
  for (auto &module : modules) {
    if ((libcMainFn = module->getFunction(libcMainFunction)))
      break;
  }
  if (!libcMainFn)
    klee_error("Could not add %s wrapper", libcMainFunction.str().c_str());

  auto inModuleRefernce = libcMainFn->getParent()->getOrInsertFunction(
      userMainFn->getName(), userMainFn->getFunctionType());

  const auto ft = libcMainFn->getFunctionType();

  if (ft->getNumParams() != 7)
    klee_error("Imported %s wrapper does not have the correct "
               "number of arguments",
               libcMainFunction.str().c_str());

  std::vector<Type *> fArgs;
  fArgs.push_back(ft->getParamType(1)); // argc
  fArgs.push_back(ft->getParamType(2)); // argv
  Function *stub =
      Function::Create(FunctionType::get(Type::getInt32Ty(ctx), fArgs, false),
                       GlobalVariable::ExternalLinkage, intendedFunction,
                       libcMainFn->getParent());
  BasicBlock *bb = BasicBlock::Create(ctx, "entry", stub);
  llvm::IRBuilder<> Builder(bb);

  std::vector<llvm::Value*> args;
  args.push_back(
      llvm::ConstantExpr::getBitCast(inModuleRefernce, ft->getParamType(0)));
  args.push_back(&*(stub->arg_begin())); // argc
  auto arg_it = stub->arg_begin();
  args.push_back(&*(++arg_it)); // argv
  args.push_back(Constant::getNullValue(ft->getParamType(3))); // app_init
  args.push_back(Constant::getNullValue(ft->getParamType(4))); // app_fini
  args.push_back(Constant::getNullValue(ft->getParamType(5))); // rtld_fini
  args.push_back(Constant::getNullValue(ft->getParamType(6))); // stack_end
  Builder.CreateCall(libcMainFn, args);
  Builder.CreateUnreachable();
}

static void
linkWithUclibc(StringRef libDir,
               std::vector<std::unique_ptr<llvm::Module>> &modules) {
  LLVMContext &ctx = modules[0]->getContext();

  size_t newModules = modules.size();

  // Ensure that klee-uclibc exists
  SmallString<128> uclibcBCA(libDir);
  std::string errorMsg;
  llvm::sys::path::append(uclibcBCA, KLEE_UCLIBC_BCA_NAME);
  if (!klee::loadFile(uclibcBCA.c_str(), ctx, modules, errorMsg))
    klee_error("Cannot find klee-uclibc '%s': %s", uclibcBCA.c_str(),
               errorMsg.c_str());

  for (auto i = newModules, j = modules.size(); i < j; ++i) {
    replaceOrRenameFunction(modules[i].get(), "__libc_open", "open");
    replaceOrRenameFunction(modules[i].get(), "__libc_fcntl", "fcntl");
  }

  createLibCWrapper(modules, EntryPoint, "__uClibc_main");
  klee_message("NOTE: Using klee-uclibc : %s", uclibcBCA.c_str());
}
#endif

bool parseNameLineOption(
    std::string option,
    std::string &fname,
    unsigned int &line) {
    std::istringstream stream(option);
    std::string token;
    char *endptr;

    if (std::getline(stream, token, ':')) {
        fname = token;
        while (std::getline(stream, token, '/')) {
            /* TODO: handle errors */
            const char *s = token.c_str();
            line = strtol(s, &endptr, 10);
            if ((errno == ERANGE) || (endptr == s) || (*endptr != '\0')) {
                return false;
            }
        }
    }
    return true;
}

int launchKleeInstance(int x, int argc, char **argv, char **envp,
    std::deque<std::string> &workList,
    std::vector<unsigned char> &prefix, 
    int explorationDepth=0, int mode=NO_MODE, std::string searchMode="BFS");
void master(int argc, char **argv, char **envp);
void slave(int argc, char **argv, char **envp);

int watchDog() {

  if (Watchdog) {
    if (MaxTime.empty()) {
      klee_error("--watchdog used without --max-time");
    }
    int pid = fork();
    if (pid<0) {
      klee_error("unable to fork watchdog");
    } else if (pid) {
      klee_message("KLEE: WATCHDOG: watching %d\n", pid);
      fflush(stderr);
      sys::SetInterruptFunction(interrupt_handle_watchdog);
      
      const time::Span maxTime(MaxTime);
      auto nextStep = time::getWallTime() + maxTime + (maxTime / 10);
      int level = 0;

      // Simple stupid code...
      while (1) {
        sleep(1);

        int status, res = waitpid(pid, &status, WNOHANG);

        if (res < 0) {
          if (errno==ECHILD) { // No child, no need to watch but
                               // return error since we didn't catch
                               // the exit.
            klee_warning("KLEE: watchdog exiting (no child)\n");
            return 1;
          } else if (errno!=EINTR) {
            perror("watchdog waitpid");
            exit(1);
          }
        } else if (res==pid && WIFEXITED(status)) {
          return WEXITSTATUS(status);
        } else {
          auto time = time::getWallTime();

          if (time > nextStep) {
            ++level;
            std::cout << "calling MPI abort\n"; 
            MPI_Abort(MPI_COMM_WORLD, -1);

            if (level==1) {
              klee_warning(
                  "KLEE: WATCHDOG: time expired, attempting halt via INT\n");
              kill(pid, SIGINT);
            } else if (level==2) {
              klee_warning(
                  "KLEE: WATCHDOG: time expired, attempting halt via gdb\n");
              halt_via_gdb(pid);
            } else {
              klee_warning(
                  "KLEE: WATCHDOG: kill(9)ing child (I tried to be nice)\n");
              kill(pid, SIGKILL);
              return 1; // what more can we do
            }

            // Ideally this triggers a dump, which may take a while,
            // so try and give the process extra time to clean up.
            auto max = std::max(time::seconds(15), maxTime / 10);
            nextStep = time::getWallTime() + max;
          }
        }
      }
      return 0;
    }
  }
  return 0;
}

void timeOutCheck() {
  sleep(int(timeOut));
  char dummy;
  MPI_Send(&dummy, 1, MPI_CHAR, 0, TIMEOUT, MPI_COMM_WORLD);
}

int main(int argc, char **argv, char **envp) {
  atexit(llvm_shutdown);  // Call llvm_shutdown() on exit.

  llvm::InitializeNativeTarget();
  
  parseArguments(argc, argv);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 9)
    sys::PrintStackTraceOnErrorSignal(argv[0]);
#else
    sys::PrintStackTraceOnErrorSignal();
#endif

  /*MPI Parallel Code should go here*/
  MPI_Init(NULL, NULL);

  int world_rank;
  MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);
  //master rank 
  if(world_rank == 0) {
    master(argc, argv, envp);
  } else if(world_rank == 1) {
    timeOutCheck();
  } else { //slaves
    slave(argc, argv, envp);
  }

  MPI_Finalize();
  return 0;
}

std::string getNewSearch() {
  if(searchPolicy == "BFS") {
    return "BFS";
  } else if (searchPolicy == "DFS") {
    return "DFS";
  } else if (searchPolicy == "RAND") {
    return "RAND";
  } else if (searchPolicy == "COVNEW") {
    return "COVNEW";
  } else {
    return "DFS";
  }
}

void mpi_pack_data(std::vector<std::pair<std::string, std::vector<unsigned char>>> &testInput, 
    std::vector<unsigned char> &mpipkt) {
  for(int x=0; x<testInput.size(); x++) {
    std::string objName = testInput[x].first;
    //std::vector<unsigned char> nameVec(objName.begin(), objName.end());
    std::copy(objName.begin(), objName.end(), std::back_inserter(mpipkt));
    mpipkt.push_back('-');
    mpipkt.insert(mpipkt.end(), testInput[x].second.begin(), testInput[x].second.end());

  }
}


void master(int argc, char **argv, char **envp) {
  auto startTime = std::time(nullptr);
  { // output clock info and start time
    std::stringstream startInfo;
    startInfo << time::getClockInfo()
              << "Started: "
              << std::put_time(std::localtime(&startTime), "%Y-%m-%d %H:%M:%S")<<'\n';
    //handler->getInfoStream() << startInfo.str();
    //handler->getInfoStream().flush();
    std::cout<< "Started: "<< std::put_time(std::localtime(&startTime), "%Y-%m-%d %H:%M:%S")<<'\n';
  }

  auto stTime = time::getWallTime();

  typedef std::vector<std::pair<std::string, std::vector<unsigned char>>> testPacket;

  //std::deque<std::deque<unsigned char>> workList;
  std::deque<std::string> workList;
  std::vector<unsigned char> dummyprefix;
  std::deque<unsigned int> freeList;
  std::deque<unsigned int> offloadActiveList;
  std::deque<unsigned int> busyList;
  std::deque<unsigned int> offloadReadyList;
  MPI_Status status;
  MPI_Status status1;
  MPI_Status status2;
  int num_cores;
  MPI_Comm_size(MPI_COMM_WORLD, &num_cores);
  std::ofstream masterLog;
  masterLog.open("log_master_"+OutputDir);
  masterLog << "MASTER_START \n";

  //*************Running Phase 1****************
  if(phase1Depth != 0) { 
    launchKleeInstance(0, argc, argv, envp, workList, dummyprefix, phase1Depth, NO_MODE, "BFS");
  } else { //single core mode, just get a worker to launck a normal klee instance, only to be 
    //used with 3 cores
    char dummychar;
    MPI_Status status3;
    MPI_Status status4;
    MPI_Send(&dummychar, 1, MPI_CHAR, 2, NORMAL_TASK, MPI_COMM_WORLD);
    MPI_Recv(&dummychar, 1, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &status3);
    std::cout << "HYHY: "<<status3.MPI_SOURCE<<" "<<status3.MPI_TAG<<"\n";
    if(status3.MPI_TAG == FINISH) {
      masterLog << "MASTER_ELAPSED Normal Mode \n";
      time::Span elapsed_time1(time::getWallTime() - stTime);
      masterLog << "Time: "<<elapsed_time1<<"\n";
      if(FLUSH) masterLog.flush();
      MPI_Send(&dummychar, 1, MPI_CHAR, 2, KILL, MPI_COMM_WORLD);
      MPI_Recv(&dummychar, 1, MPI_CHAR, 2, KILL_COMP, MPI_COMM_WORLD, &status4);
    } else if(status3.MPI_TAG == TIMEOUT) {
      masterLog << "MASTER_ELAPSED Timeout: \n";
    } else if(status3.MPI_TAG == BUG_FOUND) {
      masterLog << "WORKER->MASTER:  BUG FOUND:"<<status3.MPI_SOURCE<<"\n";
      time::Span elapsed_time1(time::getWallTime() - stTime);
      masterLog << "Time: "<<elapsed_time1<<"\n";
    }
    masterLog.close();
    //std::cout << "HUHU\n";
    MPI_Abort(MPI_COMM_WORLD, -1);
  }

  //*************Seeding the slaves*************
  int currRank = 2;
  auto wListIt = workList.begin();
  while(wListIt != workList.end() && currRank<num_cores) {
    std::cout << "Starting worker: "<<currRank<<"\n";
    masterLog << "MASTER->WORKER: START_WORK ID:"<<currRank<<"\n";
    MPI_Send(&((*wListIt)[0]), (*wListIt).size(), MPI_CHAR, currRank, START_PREFIX_TASK, MPI_COMM_WORLD);
    busyList.push_back(currRank);
    wListIt = workList.erase(wListIt);
    ++currRank;
  }

  //If worklist size is smaller than cores, kill the rest of the processes
  while(currRank < num_cores) {
    if(!lb) {
      char dummy2;
      MPI_Send(&dummy2, 1, MPI_CHAR, currRank, KILL, MPI_COMM_WORLD);
      std::cout << "Killing(not required) worker: "<<currRank<<"\n";
      masterLog << "MASTER->WORKER: KILL ID:"<<currRank<<"\n";
    }
    freeList.push_back(currRank);
    ++currRank; 
  }

  //receive FINISH/BUG FOUND/OFFLOAD READY/NOT READY messages 
  //from workers and offload further work
  char dummyRecv;
  auto currPrefix = workList.begin();
  while(currPrefix != workList.end() && (workList.size()>0)) {
    MPI_Recv(&dummyRecv, 1, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
    if(status.MPI_TAG == FINISH) {
      for(auto it = busyList.begin(); it != busyList.end(); ++it) {
        if (*it == status.MPI_SOURCE) {
          busyList.erase(it);
          break;
         }
      }
      //also remove from offloadReadyList if it exists
      for(auto it = offloadActiveList.begin(); it != offloadActiveList.end(); ++it) {
        if (*it == status.MPI_SOURCE) {
          offloadActiveList.erase(it);
          break;
        }
      }

      masterLog << "WORKER->MASTER: FINISH ID:"<<status.MPI_SOURCE<<"\n";
      MPI_Send(&((*currPrefix)[0]), (*currPrefix).size(), MPI_CHAR, status.MPI_SOURCE, 
        START_PREFIX_TASK, MPI_COMM_WORLD);
      currPrefix = workList.erase(currPrefix);
      masterLog << "MASTER->WORKER: START_WORK ID:"<<status.MPI_SOURCE<<"\n";
      busyList.push_back(status.MPI_SOURCE);
    } else if(status.MPI_TAG == BUG_FOUND) {
      masterLog << "WORKER->MASTER:  BUG FOUND:"<<status.MPI_SOURCE<<"\n";
      time::Span elapsed_time1(time::getWallTime() - stTime);
      masterLog << "Time: "<<elapsed_time1<<"\n";
      masterLog.close(); 
      char dummy;
      for(int x=2; x<num_cores; ++x) {
        MPI_Send(&dummy, 1, MPI_CHAR, x, KILL, MPI_COMM_WORLD);
      }
    } else if(status.MPI_TAG == READY_TO_OFFLOAD) {
      //masterLog << "WORKER->MASTER: READY TO OFFLOAD:"<<status.MPI_SOURCE<<"\n";
      offloadReadyList.push_back(status.MPI_SOURCE);
    } else if(status.MPI_TAG == NOT_READY_TO_OFFLOAD) {
      bool found2Erase=false;
      //masterLog << "WORKER->MASTER: NOT READY TO OFFLOAD:"<<status.MPI_SOURCE<<"\n";
      for(auto it=offloadReadyList.begin(); it!=offloadReadyList.end(); ++it) {
        if(*it==status.MPI_SOURCE) {
          offloadReadyList.erase(it);
          found2Erase=true;
          break;
        }
      }
      assert(found2Erase);
    } else {
      //should not see any tags here
      bool ok = false;
      (void) ok;
      assert(ok && "MASTER received an illegal tag");
    } 
  }

  masterLog << "MASTER: DONE_WITH_ALL_PREFIXES\n";
	bool offloadActive = false;
  //once done with the initial prefixes offload when a worker becomes free 
  while(true) {
    MPI_Status status;
    int flag, count;
    char *buffer;
    //see what the workers are saying
    MPI_Iprobe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &flag, &status);

    if(flag) {
      MPI_Get_count(&status, MPI_CHAR, &count);
      buffer = (char*)malloc(count+1);
      MPI_Recv(buffer, count, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
      if(status.MPI_TAG == BUG_FOUND) {
        masterLog << "WORKER->MASTER: BUG FOUND:"<<status.MPI_SOURCE<<"\n";
        time::Span elapsed_time1(time::getWallTime() - stTime);
        masterLog << "Time: "<<elapsed_time1<<"\n";
        masterLog.close();
        
        char dummy;
        for(int x=2; x<num_cores; ++x) {
          MPI_Send(&dummy, 1, MPI_CHAR, x, KILL, MPI_COMM_WORLD);
        }

        //MPI_Abort(MPI_COMM_WORLD, -1);
      } else if(status.MPI_TAG == FINISH) {
        bool ffound=0;
        for(auto it=freeList.begin(); it!=freeList.end(); ++it) {
          if(*it == status.MPI_SOURCE) {
            ffound=1;
            break;
          } 
        }
        if(!ffound) freeList.push_back(status.MPI_SOURCE);

        for(auto it = busyList.begin(); it != busyList.end(); ++it) {
          if (*it == status.MPI_SOURCE) {
            busyList.erase(it);
            break;
           }
        }

				//also remove from offloadReadyList if it exists
				for(auto it = offloadActiveList.begin(); it != offloadActiveList.end(); ++it) {
  				if (*it == status.MPI_SOURCE) {
    				offloadActiveList.erase(it);
    				break;
 					}
				}

        masterLog << "WORKER->MASTER: FINISH ID:"<<status.MPI_SOURCE<<"\n";
        masterLog << "WORKER->MASTER: FREELIST SIZE:"<<freeList.size()<<"\n";
        if(FLUSH) masterLog.flush();
        //if all workers finish then shut down the system
        if(freeList.size() == (num_cores-2)) {
          masterLog << "MASTER: ALL WORKERS FINISHED \n";
          if(FLUSH) masterLog.flush();
          
          //Kill all the workers
          char dummy;
          for(int x=2; x<num_cores; ++x) {
              MPI_Send(&dummy, 1, MPI_CHAR, x, KILL, MPI_COMM_WORLD);
          }

          masterLog << "MASTER_ELAPSED: \n";
          time::Span elapsed_time2(time::getWallTime() - stTime);
          masterLog << "Time: "<<elapsed_time2<<"\n";
          masterLog.close();
          
          for(int x=2; x<num_cores; ++x) {
            MPI_Recv(&dummy, 1, MPI_CHAR, x, KILL_COMP, MPI_COMM_WORLD, &status2);
          }
          MPI_Abort(MPI_COMM_WORLD, -1);
        }
      } else if(status.MPI_TAG == TIMEOUT) {
        char dummy;
        for(int x=2; x<num_cores; ++x) {
          MPI_Send(&dummy, 1, MPI_CHAR, x, KILL, MPI_COMM_WORLD);
        }
      } else if(status.MPI_TAG == READY_TO_OFFLOAD) {
        //masterLog << "WORKER->MASTER: READY TO OFFLOAD:"<<status.MPI_SOURCE<<"\n";
        offloadReadyList.push_back(status.MPI_SOURCE);
      } else if(status.MPI_TAG == NOT_READY_TO_OFFLOAD) {
        bool found2Erase=false;
        //masterLog << "WORKER->MASTER: NOT READY TO OFFLOAD:"<<status.MPI_SOURCE<<"\n";
        for(auto it=offloadReadyList.begin(); it!=offloadReadyList.end(); ++it) {
          if(*it==status.MPI_SOURCE) {
            offloadReadyList.erase(it);
            found2Erase=true;
            break;
          }
        }
        assert(found2Erase);
      } else if(status.MPI_TAG == OFFLOAD_RESP) {
				masterLog << "WORKER->MASTER: OFFLOAD RCVD ID:"<<status.MPI_SOURCE<<" Length:"<<count<<"\n";
				if(FLUSH) masterLog.flush();

				//Removing the offload active list worker 
				for(auto it = offloadActiveList.begin(); it != offloadActiveList.end(); ++it) {
  				if (*it == status.MPI_SOURCE) {
    				offloadActiveList.erase(it);
						break;
					}
				}

				//Send the offloaded work to the free worker 
				if(count>4) {
					//something should exist in free list
					assert(freeList.size() > 0);
  				unsigned int pickedWorker = freeList.front();
  				masterLog << "MASTER->WORKER: PREFIX_TASK_SEND ID:"<<pickedWorker<<" Length:"<<count<<"\n";
  				MPI_Send(buffer, count, MPI_CHAR, pickedWorker, START_PREFIX_TASK, MPI_COMM_WORLD);
  				masterLog << "MASTER->WORKER: START_WORK ID:"<<pickedWorker<<"\n";
  				//pushing the worker busy list
  				busyList.push_back(pickedWorker);
 	 				freeList.pop_front();
				}		
				offloadActive = false;	 
      } 
      else {
        //should not see any tags here
        std::cout << "ILLEGAL TAG: "<<status.MPI_TAG<<" "<<status.MPI_SOURCE<<"\n";
        if(FLUSH) std::cout.flush();
        bool ok = false;
        (void) ok;
        assert(ok && "MASTER received an illegal tag"); 
      }
    }

    //if some workers are ready to offload and freelist has some workers
		//offload some stuff
    if(lb && (freeList.size()>0) && (freeList.size()<(num_cores-2))
        && (offloadReadyList.size()>0) && !offloadActive) {

      //pick out the worker that has been busy the longest and to whom an
      //offload request in not yet sent
      bool foundWorker2Offload = false;
      unsigned int worker2offload;
      for(auto it = offloadReadyList.begin(); it != offloadReadyList.end(); ++it) {
        bool offloadAlreadySent = false;
        for(auto it2 = offloadActiveList.begin(); it2 < offloadActiveList.end(); ++it2) {
          if(*it == *it2) {
            offloadAlreadySent = true;
            break;
          } 
        }
        if(!offloadAlreadySent) {
          foundWorker2Offload = true;
          worker2offload = *it;
          offloadActiveList.push_back(worker2offload);
          break;
        }
      }
      //found a valid busy worker
      if(foundWorker2Offload) {
        MPI_Status offloadStatus;
        char dummyBuff;
        MPI_Send(&dummyBuff, 1, MPI_CHAR, worker2offload, OFFLOAD, MPI_COMM_WORLD);
        masterLog << "MASTER->WORKER: OFFLOAD_SENT ID:"<<worker2offload<<"\n";
        if(FLUSH) masterLog.flush();
				offloadActive = true;
      }
    }
	}
}

void slave(int argc, char **argv, char **envp) {
  int world_rank;
  MPI_Status status;
  char result;
  std::deque<std::string> dummyworkList;
  MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);
  while(true) {
    //trying to check the TAG of incoming message
    MPI_Status status;
    MPI_Probe(0, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
    int count;
    MPI_Get_count(&status, MPI_CHAR, &count);

    if(status.MPI_TAG == KILL) {
      char dummy2;
      MPI_Recv(&dummy2, 1, MPI_CHAR, 0, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
      std::cout << "Killing Process: "<<world_rank<<"\n";
      return;

    } else if(status.MPI_TAG == START_PREFIX_TASK) {
      //std::vector<std::pair<std::string, std::vector<unsigned char>>> recvTest;
      std::vector<unsigned char> recvTest;
      recvTest.resize(count);
      MPI_Recv(&recvTest[0], count, MPI_CHAR, 0, MPI_ANY_TAG, MPI_COMM_WORLD, &status);
      std::cout << "Process: "<<world_rank<<" Prefix Task: Length:"<<count<<"\n";
      launchKleeInstance(world_rank, argc, argv, envp, 
        dummyworkList, recvTest, phase2Depth, PREFIX_MODE, getNewSearch());
      std::cout << "Cleanup Complete: " << world_rank << "\n";
      //MPI_Send(&result, 1, MPI_CHAR, 0, FINISH, MPI_COMM_WORLD);
      MPI_Send(&result, 1, MPI_CHAR, 0, KILL_COMP, MPI_COMM_WORLD);
      return;

    } else if(status.MPI_TAG == NORMAL_TASK) {
      char buffer;
  		MPI_Recv(&buffer, count, MPI_CHAR, MASTER_NODE, NORMAL_TASK, MPI_COMM_WORLD, &status);
      std::cout << "Process: "<<world_rank<<" Normal Task "<<"Prefix Depth: "<<phase2Depth<<"\n";
      std::vector<unsigned char> recvTest;
      recvTest.resize(count);
      launchKleeInstance(world_rank, argc, argv, envp,
        dummyworkList, recvTest, phase2Depth, NO_MODE, getNewSearch());
      MPI_Send(&result, 1, MPI_CHAR, 0, KILL_COMP, MPI_COMM_WORLD);
      return;

    } else if(status.MPI_TAG == OFFLOAD) {
      char buffer;
  		MPI_Recv(&buffer, count, MPI_CHAR, MASTER_NODE, OFFLOAD, MPI_COMM_WORLD, &status);
      std::cout << "Caught the offload here: "<<world_rank<<"\n";
      if(FLUSH) std::cout.flush();
      std::string pkt2Send = "x";
  		MPI_Send(pkt2Send.c_str(), pkt2Send.length(), MPI_CHAR, 0, OFFLOAD_RESP, MPI_COMM_WORLD);
    }
  }
}

int launchKleeInstance(int x, int argc, char **argv, char **envp,
    std::deque<std::string> &workList,
    std::vector<unsigned char> &prefix, 
    int explorationDepth, int mode, std::string searchMode) {

	// Load the bytecode...
	std::string errorMsg;
	LLVMContext ctx;
	std::vector<std::unique_ptr<llvm::Module>> loadedModules;
	if (!klee::loadFile(InputFile, ctx, loadedModules, errorMsg)) {
		klee_error("error loading program '%s': %s", InputFile.c_str(),
							 errorMsg.c_str());
	}
	// Load and link the whole files content. The assumption is that this is the
	// application under test.
	// Nothing gets removed in the first place.
	std::unique_ptr<llvm::Module> M(klee::linkModules(
			loadedModules, "" /* link all modules together */, errorMsg));
	if (!M) {
		klee_error("error loading program '%s': %s", InputFile.c_str(),
							 errorMsg.c_str());
	}

	llvm::Module *mainModule = M.get();
	// Push the module as the first entry
	loadedModules.emplace_back(std::move(M));

	std::string LibraryDir = KleeHandler::getRunTimeLibraryPath(argv[0]);
	Interpreter::ModuleOptions Opts(LibraryDir.c_str(), EntryPoint,
																	/*Optimize=*/OptimizeModule,
																	/*CheckDivZero=*/CheckDivZero,
																	/*CheckOvershift=*/CheckOvershift);

	if (WithPOSIXRuntime) {
		SmallString<128> Path(Opts.LibraryDir);
		llvm::sys::path::append(Path, "libkleeRuntimePOSIX.bca");
		klee_message("NOTE: Using POSIX model: %s", Path.c_str());
		if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
												errorMsg))
			klee_error("error loading POSIX support '%s': %s", Path.c_str(),
								 errorMsg.c_str());
    
		std::string libcPrefix = (Libc == LibcType::UcLibc ? "__user_" : "");
		preparePOSIX(loadedModules, libcPrefix);
	}
	switch (Libc) {
    case LibcType::KleeLibc: {
      // FIXME: Find a reasonable solution for this.
      SmallString<128> Path(Opts.LibraryDir);
      llvm::sys::path::append(Path, "libklee-libc.bca");
      if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
                          errorMsg))
        klee_error("error loading klee libc '%s': %s", Path.c_str(),
                   errorMsg.c_str());
    }
    /* Falls through. */
    case LibcType::FreeStandingLibc: {
      SmallString<128> Path(Opts.LibraryDir);
      llvm::sys::path::append(Path, "libkleeRuntimeFreeStanding.bca");
      if (!klee::loadFile(Path.c_str(), mainModule->getContext(), loadedModules,
                          errorMsg))
        klee_error("error loading free standing support '%s': %s", Path.c_str(),
                   errorMsg.c_str());
      break;
    }
    case LibcType::UcLibc:
      linkWithUclibc(LibraryDir, loadedModules);
      break;
	}

	for (const auto &library : LinkLibraries) {
		if (!klee::loadFile(library, mainModule->getContext(), loadedModules,
												errorMsg))
			klee_error("error loading free standing support '%s': %s",
								 library.c_str(), errorMsg.c_str());
	}


  // FIXME: Change me to std types.
  int pArgc;
  char **pArgv;
  char **pEnvp;
  if (Environ != "") {
    std::vector<std::string> items;
    std::ifstream f(Environ.c_str());
    if (!f.good())
      klee_error("unable to open --environ file: %s", Environ.c_str());
    while (!f.eof()) {
      std::string line;
      std::getline(f, line);
      line = strip(line);
      if (!line.empty())
        items.push_back(line);
    }
    f.close();
    pEnvp = new char *[items.size()+1];
    unsigned i=0;
    for (; i != items.size(); ++i) {
      pEnvp[i] = strdup(items[i].c_str());
    }
    pEnvp[i] = 0;
  } else {
    pEnvp = envp;
  }

  pArgc = InputArgv.size() + 1;
  pArgv = new char *[pArgc];
  for (unsigned i=0; i<InputArgv.size()+1; i++) {
    std::string &arg = (i==0 ? InputFile : InputArgv[i-1]);
    unsigned size = arg.size() + 1;
    char *pArg = new char[size];

    std::copy(arg.begin(), arg.end(), pArg);
    pArg[size - 1] = 0;

    pArgv[i] = pArg;
  }

  std::vector<bool> replayPath;

  if (ReplayPathFile != "") {
    KleeHandler::loadPathFile(ReplayPathFile, replayPath);
  }

  Interpreter::InterpreterOptions IOpts;
  IOpts.MakeConcreteSymbolic = MakeConcreteSymbolic;
  KleeHandler *handler = new KleeHandler(pArgc, pArgv);
  Interpreter *interpreter =
    theInterpreter = Interpreter::create(ctx, IOpts, handler);
  handler->setInterpreter(interpreter);

  for (int i=0; i<argc; i++) {
    handler->getInfoStream() << argv[i] << (i+1<argc ? " ":"\n");
  }
  handler->getInfoStream() << "PID: " << getpid() << "\n";

  // Get the desired main function.  klee_main initializes uClibc
  // locale and other data and then calls main.

	auto finalModule = interpreter->setModule(loadedModules, Opts);
	Function *mainFn = finalModule->getFunction(EntryPoint);
	if (!mainFn) {
  	klee_error("Entry function '%s' not found in module.", EntryPoint.c_str());
	}

	externalsAndGlobalsCheck(finalModule);

  if (!ReplayKTestDir.empty() || !ReplayKTestFile.empty()) {
    assert(SeedOutFile.empty());
    assert(SeedOutDir.empty());
  
    std::vector<std::string> kTestFiles = ReplayKTestFile;
    for (std::vector<std::string>::iterator
           it = ReplayKTestDir.begin(), ie = ReplayKTestDir.end();
         it != ie; ++it)
      KleeHandler::getKTestFilesInDir(*it, kTestFiles);
    std::vector<KTest*> kTests;
    for (std::vector<std::string>::iterator
           it = kTestFiles.begin(), ie = kTestFiles.end();
         it != ie; ++it) {
      KTest *out = kTest_fromFile(it->c_str());
      if (out) {
        kTests.push_back(out);
      } else {
        klee_warning("unable to open: %s\n", (*it).c_str());
      }
    }

    if (RunInDir != "") {
      int res = chdir(RunInDir.c_str());
      if (res < 0) {
        klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                   sys::StrError(errno).c_str());
      }
    }

    unsigned i=0;
    for (std::vector<KTest*>::iterator
           it = kTests.begin(), ie = kTests.end();
         it != ie; ++it) {
      KTest *out = *it;
      interpreter->setReplayKTest(out);
      llvm::errs() << "KLEE: replaying: " << *it << " (" << kTest_numBytes(out)
                   << " bytes)"
                   << " (" << ++i << "/" << kTestFiles.size() << ")\n";
      // XXX should put envp in .ktest ?
      interpreter->runFunctionAsMain(mainFn, out->numArgs, out->args, pEnvp, false);
      if (interrupted) break;
    }
    interpreter->setReplayKTest(0);
    while (!kTests.empty()) {
      kTest_free(kTests.back());
      kTests.pop_back();
    }
  } else {
    std::vector<KTest *> seeds;
    for (std::vector<std::string>::iterator
           it = SeedOutFile.begin(), ie = SeedOutFile.end();
         it != ie; ++it) {
      KTest *out = kTest_fromFile(it->c_str());
      if (!out) {
        klee_error("unable to open: %s\n", (*it).c_str());
      }
      seeds.push_back(out);
    }
    for (std::vector<std::string>::iterator
           it = SeedOutDir.begin(), ie = SeedOutDir.end();
         it != ie; ++it) {
      std::vector<std::string> kTestFiles;
      KleeHandler::getKTestFilesInDir(*it, kTestFiles);
      for (std::vector<std::string>::iterator
             it2 = kTestFiles.begin(), ie = kTestFiles.end();
           it2 != ie; ++it2) {
        KTest *out = kTest_fromFile(it2->c_str());
        if (!out) {
          klee_error("unable to open: %s\n", (*it2).c_str());
        }
        seeds.push_back(out);
      }
      if (kTestFiles.empty()) {
        klee_error("seeds directory is empty: %s\n", (*it).c_str());
      }
    }

    if (!seeds.empty()) {
      klee_message("KLEE: using %lu seeds\n", seeds.size());
      interpreter->useSeeds(&seeds);
    }
    if (RunInDir != "") {
      int res = chdir(RunInDir.c_str());
      if (res < 0) {
        klee_error("Unable to change directory to: %s - %s", RunInDir.c_str(),
                   sys::StrError(errno).c_str());
      }
    }

    if(explorationDepth != 0) {
      interpreter->setExplorationDepth(explorationDepth);
    }

    if(mode == PREFIX_MODE) {
			std::string pktest(prefix.begin(), prefix.end());
			std::cout << "Prefixed Received: "<<pktest<<"\n";

			char *pch;
			pch = strtok(&pktest[0], ",");
			int count = 0;
			while(pch!=NULL) {
				std::string ff(pch);
				std::cout<<ff<<"\n";
				if(count == 0) {
					KTest *out = kTest_fromFile(ff.c_str());
					if (out) {
						interpreter->setPrefixKTest(out, ff);
					} else {
						klee_warning("unable to open: %s\n", ff);
					}
				} else {
					interpreter->setTestPrefixDepth(std::stoi(ff));
				}
				++count;
				pch = strtok(NULL, ",");
			}
    } 

    if(ErrorLocation != "none") {
      std::string fname;
      unsigned int line;
      if(parseNameLineOption(ErrorLocation, fname, line)) {
        interpreter->setErrorPair(std::make_pair(fname, line));
      } else {
        klee_error("INVALID Error Location Arguments");
      }
    }
	  
    int world_rank;
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank);
    std::string output_dir_file;
    std::string pthfile;

    interpreter->enableLoadBalancing(lb);

    interpreter->setSearchMode(searchMode);
    pthfile = handler->getOutputDir()+"_pathFile_"+std::to_string(x);
    interpreter->setPathFile(pthfile);

    output_dir_file = handler->getOutputDir();
    interpreter->setBrHistFile(output_dir_file+"_br_hist");
    interpreter->setErrorFile(errorFile);
    interpreter->setLogFile(output_dir_file+"_log_file");
    interpreter->setOutputDir(output_dir_file);
    std::cout << "Setting log file: "<<output_dir_file+"_log_file"<<"\n";

    interpreter->runFunctionAsMain2(mainFn, pArgc, pArgv, pEnvp, workList);

    while (!seeds.empty()) {
      kTest_free(seeds.back());
      seeds.pop_back();
    }
  }

  //t[1] = time(NULL);
  //strftime(buf, sizeof(buf), "Finished: %Y-%m-%d %H:%M:%S\n", localtime(&t[1]));
  //handler->getInfoStream() << buf;

  //strcpy(buf, "Elapsed: ");
  //strcpy(format_tdiff(buf, t[1] - t[0]), "\n");
  //handler->getInfoStream() << buf;

  // Free all the args.
  for (unsigned i=0; i<InputArgv.size()+1; i++)
    delete[] pArgv[i];
  delete[] pArgv;

  delete interpreter;

  uint64_t queries =
    *theStatisticManager->getStatisticByName("Queries");
  uint64_t queriesValid =
    *theStatisticManager->getStatisticByName("QueriesValid");
  uint64_t queriesInvalid =
    *theStatisticManager->getStatisticByName("QueriesInvalid");
  uint64_t queryCounterexamples =
    *theStatisticManager->getStatisticByName("QueriesCEX");
  uint64_t queryConstructs =
    *theStatisticManager->getStatisticByName("QueriesConstructs");
  uint64_t instructions =
    *theStatisticManager->getStatisticByName("Instructions");
  uint64_t forks =
    *theStatisticManager->getStatisticByName("Forks");

  handler->getInfoStream()
    << "KLEE: done: explored paths = " << 1 + forks << "\n";

  // Write some extra information in the info file which users won't
  // necessarily care about or understand.
  if (queries)
    handler->getInfoStream()
      << "KLEE: done: avg. constructs per query = "
                             << queryConstructs / queries << "\n";
  handler->getInfoStream()
    << "KLEE: done: total queries = " << queries << "\n"
    << "KLEE: done: valid queries = " << queriesValid << "\n"
    << "KLEE: done: invalid queries = " << queriesInvalid << "\n"
    << "KLEE: done: query cex = " << queryCounterexamples << "\n";

  std::stringstream stats;
  stats << "\n";
  stats << "KLEE: done: total instructions = "
        << instructions << "\n";
  stats << "KLEE: done: completed paths = "
        << handler->getNumPathsExplored() << "\n";
  stats << "KLEE: done: generated tests = "
        << handler->getNumTestCases() << "\n";

  bool useColors = llvm::errs().is_displayed();
  if (useColors)
    llvm::errs().changeColor(llvm::raw_ostream::GREEN,
                             /*bold=*/true,
                             /*bg=*/false);

  llvm::errs() << stats.str();

  if (useColors)
    llvm::errs().resetColor();

  handler->getInfoStream() << stats.str();

  //remove the br_hist file path files log files and directory
  /*if(ENABLE_CLEANUP) {
    std::string brhist = output_dir_file+"_br_hist";
    const char * c = brhist.c_str();
    std::string logfile = output_dir_file+"_log_file";
    const char * d = logfile.c_str();
    const char * e = output_dir_file.c_str();
    std::string pathfile = pthfile; 
    const char * f = pthfile.c_str();
    std::string a1 = output_dir_file+"/assembly.ll";
    const char * a = a1.c_str();
    std::string b1 = output_dir_file+"/info";
    const char * b = b1.c_str();
    std::string x1 = output_dir_file+"/messages.txt";
    const char * x = x1.c_str();
    std::string z1 = output_dir_file+"/warnings.txt";
    const char * z = z1.c_str();
    remove(c);
    remove(d);
    remove(f);
    remove(a);
    remove(b);
    remove(x);
    remove(z);
    rmdir(e);
    std::cout <<"Deleteing dir: "<<output_dir_file<<"\n";
  }*/
  
  delete handler;
  mainModule = NULL;
  return 0;
}
