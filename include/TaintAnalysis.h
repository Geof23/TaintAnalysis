#pragma once

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Value.h"
#include "llvm/MDBuilder.h"
#include "llvm/BasicBlock.h"
#include "llvm/Module.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/GlobalValue.h"
#include "llvm/User.h"
#include "llvm/Argument.h"
#include "llvm/InitializePasses.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/CallSite.h"
#include "llvm/PassSupport.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/DebugInfo.h"
#include "TaintInliner.h"

#include <set>
#include <vector>
#include <algorithm>
#include <iostream>
#include <iterator>
#include <map>

#define TAINT_INFO2 std::cout << "[TAINT]: "

using namespace llvm;

namespace taint {

struct RelValue {
  llvm::Instruction *inst;
  llvm::Value *relVal;
 
  RelValue(llvm::Instruction *_inst, 
           llvm::Value *_val) : inst(_inst), 
                                relVal(_val) {} 
};

struct RelFlowSet {
  std::vector<RelValue> sharedReadVec;
  std::vector<RelValue> sharedWriteVec;
  std::vector<RelValue> globalReadVec;
  std::vector<RelValue> globalWriteVec;

  RelFlowSet() {};

  bool empty() {
    return sharedReadVec.empty() 
             && sharedWriteVec.empty()
               && globalReadVec.empty()
                 && globalWriteVec.empty();
  }

  ~RelFlowSet() {
    sharedReadVec.clear();
    sharedWriteVec.clear();
    globalReadVec.clear();
    globalWriteVec.clear();
  }
};

struct CFGTaintSet {
  bool explore;
  std::set<Instruction*> instSet;

  CFGTaintSet(bool _explore, 
              std::set<Instruction*> _instSet) : explore(_explore), 
                                                 instSet(_instSet) {}

  CFGTaintSet(const CFGTaintSet &taintSet) : explore(taintSet.explore), 
                                             instSet(taintSet.instSet) {}

  ~CFGTaintSet() {
    instSet.clear();
  } 
};

struct CFGNode {
  llvm::Instruction *inst;
  llvm::BasicBlock *postDom;
  bool isBrCond;
  bool causeIteration;
  unsigned outOfIteration;
  unsigned which; // which path is being explored   
  CFGNode *parent;
  bool allFinish;
  bool tainted;
  std::vector<CFGNode*> cfgNodes;
  std::vector<CFGTaintSet> cfgInstSet;
  std::vector<RelFlowSet> cfgFlowSet;

  CFGNode *successor;
  std::set<Instruction*> succInstSet;
  RelFlowSet succFlowSet;

  CFGNode(llvm::Instruction *_inst, 
          llvm::BasicBlock *_postDom, 
          unsigned numSuccessors, 
          bool _isBrCond) : inst(_inst), 
                            postDom(_postDom), 
                            isBrCond(_isBrCond) {
    which = 0;
    parent = NULL;
    causeIteration = false;
    allFinish = false;
    tainted = false;
    std::set<Instruction*> instSet;
    for (unsigned i = 0; i < numSuccessors; i++) {
      cfgNodes.push_back(NULL);
      cfgInstSet.push_back(CFGTaintSet(false, instSet));
      cfgFlowSet.push_back(RelFlowSet());
    }
    successor = NULL;
  }

  ~CFGNode() {
    cfgNodes.clear();
    cfgInstSet.clear();
    cfgFlowSet.clear();
  }
};

struct VInstruction {
  llvm::Instruction *inst;
};

struct VFunction {
  llvm::Function *func;
  VInstruction **insts;
  VInstruction **curInst;
  std::map<llvm::BasicBlock*, unsigned> basicBlockEntry;
  unsigned numInsts;

public:
  VFunction(llvm::Function *F);
  ~VFunction();
  void restoreCurInst();
  void setCurrentInst(llvm::Instruction *curInst);
  void setCurrentInstThroughEntry(unsigned entry);
  void dumpVFunctionInst();
 
  Instruction* getCurrentInst() {
    return (*curInst)->inst;
  }

  void stepInstruction() {
    curInst++;
  }
};

struct TaintArgInfo {
  std::string fName;
  Value *arg;
  bool taint;
  unsigned argNum;  
  std::set<Instruction*> taintInstList;
  std::set<Value*> taintValueSet;

  TaintArgInfo() {};
 
  TaintArgInfo(std::string _fName, Value *_arg, 
               bool _taint, unsigned _argNum) : 
                                   fName(_fName), 
                                   arg(_arg), 
                                   taint(_taint),
                                   argNum(_argNum) {};

  TaintArgInfo(const TaintArgInfo &info) : 
                                   fName(info.fName), 
                                   arg(info.arg), 
                                   taint(info.taint), 
                                   argNum(info.argNum), 
                                   taintInstList(info.taintInstList), 
                                   taintValueSet(info.taintValueSet) {};

  ~TaintArgInfo() {
    taintInstList.clear();
    taintValueSet.clear();
  }
};

struct SharedTaint {
  Value *gv;
  std::set<Instruction*> sharedInstSet;
  std::set<Value*> sharedValueSet; 

  SharedTaint(Value *_gv) : gv(_gv) {
    sharedValueSet.insert(_gv);
  }

  ~SharedTaint() {
    sharedInstSet.clear();
    sharedValueSet.clear();
  }
};

class CFGTree {
  public: 
    std::set<Instruction*> preInstSet;
    RelFlowSet preFlowSet;

    CFGTree(); 
    ~CFGTree();
    void destroyCFGTree(CFGNode *node);
    CFGNode *getRootNode();
    CFGNode *getCurrentNode();
    CFGNode *getFlowCurrentNode();
    bool inIteration();
    void insertNodeIntoCFGTree(CFGNode *node);
    bool resetCurrentNodeInCFGTree(CFGNode *node, 
                                   llvm::Instruction *inst);
    void exploreCFGUnderIteration(llvm::Instruction *inst);
    bool isCFGTreeFullyExplored();
    unsigned getNodeNum() const {
      return nodeNum;
    }
    void insertCurInst(llvm::Instruction *inst, 
                       std::vector<TaintArgInfo> &argSet, 
                       AliasAnalysis &AA, 
                       std::vector<SharedTaint> &sharedSet);
    void setSyncthreadEncounter();
    bool exploreOneSideOfNode(CFGTaintSet &cfgTaintSet, 
                              RelFlowSet &relFlowSet, 
                              CFGNode *node, bool glAndsh);
    void exploreNodeCurrentBI(CFGNode *node, 
                              bool &singlePath, 
                              unsigned i, 
                              bool glAndsh); 
    void exploreNodeAcrossBI(CFGNode *node, 
                             bool &singlePath, 
                             unsigned i, 
                             bool glAndsh);
    void dumpNodeInstForDFSChecking(CFGNode *node, 
                                    unsigned i); 
    bool startDFSCheckingForCurrentBI(CFGNode *node); 
    void exploreCFGTreeToAnnotate(llvm::LLVMContext &glContext, 
                                  llvm::Function *f, 
                                  CFGNode *node);
    bool foundSameBrInstFromCFGTree(llvm::Instruction *inst, 
                                    CFGNode *node); 
    bool identifySuccessorRelation(llvm::BasicBlock *predBB, 
                                   llvm::BasicBlock *succBB); 
    bool enterIteration(llvm::Instruction *inst, 
                        CFGNode *current, 
                        std::set<BasicBlock*> &exploredBBSet, 
                        bool blockChange);
    void updateCurrentNode(llvm::Instruction *inst, 
                           bool &transfer);
    void setCFGNodeWithCauseIteration();
    void updateCurrentNodeAfterIteration();
    bool updateCFGTree(llvm::Instruction *inst, 
                       std::vector<TaintArgInfo> &taintArgSet, 
                       std::set<BasicBlock*> &exploredBBSet,
                       bool blockChange,
                       bool &finishIteration);
    
  private:
    unsigned nodeNum;
    CFGNode *root;
    CFGNode *current;
    CFGNode *flowCurrent;
    CFGNode* iterateCFGNode;
    std::vector<TaintArgInfo> taintInfoSet;
    bool syncthreadEncounter;
};

class TaintAnalysisCUDA : public FunctionPass {
public:
  static char ID;
  std::map<std::string, bool> kernelSet;
  std::vector<VFunction*> functions;
  std::vector<SharedTaint> sharedSet;
  VFunction* curVFunc;
  CFGTree *cfgTree;
  bool enterIteration;

  std::set<BasicBlock*> exploredBBSet;
  std::map<CFGNode*, std::vector<CFGTaintSet> > exploredCFGInst;

  TaintAnalysisCUDA() : FunctionPass(ID) {}
  void dumpTaintArgInfo(TaintArgInfo &argInfo);
  CFGTree *getCFGTree() const {
    return cfgTree;
  }

  bool dumpAliasResult(llvm::Value *pointer, AliasAnalysis &AA, 
                       std::vector<Value*> &sharedSet, 
                       unsigned &num); 
  void encounterSyncthreadsBarrier(Instruction *inst);
  void constructExploredCFGInst(); 
  void insertCurInstToCFGTree(Instruction *inst, 
                              std::vector<TaintArgInfo> &taintArgSet, 
                              AliasAnalysis &AA);
  bool exploreCUDAKernel(llvm::Function *f, 
                         AliasAnalysis &AA);
  virtual bool runOnFunction(llvm::Function &F);

  bool doInitialization(llvm::Module &M);
  VFunction* getCurrentVFunction();

  void transferToBasicBlock(llvm::BasicBlock *dst);
  void handleBrInst(llvm::Instruction *inst, 
                    std::vector<TaintArgInfo> &argSet);
  void transferToIterationPostDom(llvm::Instruction *inst); 
  void transferToAnotherSideCurrentNode();
  void handleSwitchInst(llvm::Instruction *inst,
                        std::vector<TaintArgInfo> &argSet);
  void handlePHINode(llvm::Instruction *inst, 
                     std::vector<TaintArgInfo> &argSet);
  void handleSelectInst(llvm::Instruction *inst, 
                        std::vector<TaintArgInfo> &argSet);
  void executeCall(llvm::Instruction *inst, 
                   llvm::Function *f,
                   std::vector<TaintArgInfo> &argSet, 
                   AliasAnalysis &AA);
  void executeCUDAArithOrConvIntrinsic(llvm::Instruction *inst, 
                                       std::string fName,
                                       std::vector<TaintArgInfo> &argSet);
  void executeCUDAAtomicIntrinsic(Instruction *inst, 
                                  std::string fName,
                                  std::vector<TaintArgInfo> &taintArgSet); 
  void executeCUDAIntrinsic(llvm::Instruction *inst, 
                            llvm::Function *f, 
                            std::vector<TaintArgInfo> &argSet);
  void handleArithmeticInst(llvm::Instruction *inst, 
                            std::vector<TaintArgInfo> &argSet);
  void handleCmpInst(llvm::Instruction *inst,
                     std::vector<TaintArgInfo> &argSet);
  void handleLoadInst(llvm::Instruction *inst,
                      std::vector<TaintArgInfo> &argSet, 
                      AliasAnalysis &AA);
  void handlePointerOperand(llvm::Instruction *inst, 
                            std::set<Instruction*> &instSet, 
                            std::set<Value*> &valueSet);
  void handleStoreInst(llvm::Instruction *inst, 
                       std::vector<TaintArgInfo> &argSet, 
                       AliasAnalysis &AA);
  bool checkCFGTaintSetAffected(Value* val, 
                                Instruction *inst, 
                                bool sSink);
  void checkGEPIIndex(llvm::Instruction *inst, 
                      std::vector<TaintArgInfo> &argSet);
  void handleGetElementPtrInst(llvm::Instruction *inst, 
                               std::vector<TaintArgInfo> &argSet, 
                               AliasAnalysis &AA);
  void handleConversionInst(llvm::Instruction *inst,
                            std::vector<TaintArgInfo> &argSet);
  bool executeInstruction(llvm::Instruction *inst, 
                          std::vector<TaintArgInfo> &argSet,
                          AliasAnalysis &AA);

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<TaintInliner>();
    AU.addPreserved<TaintInliner>();
    AU.addRequired<AliasAnalysis>();
    AU.addPreserved<AliasAnalysis>();
  }
};

class ExecutorUtil {
  public:
    static BasicBlock* findNearestCommonPostDominator(llvm::Instruction *inst, 
                                                      bool isCondBr); 
    static bool checkVarAliasToShared(llvm::Value *pointer, 
                                      AliasAnalysis &AA, 
                                      std::vector<SharedTaint> &sharedSet, 
                                      unsigned &num);
    static bool findValueFromTaintSet(llvm::Value *val, 
                                      std::set<Instruction*> &taintInstList, 
                                      std::set<Value*> &taintValueSet);
    static void dumpTaintInstList(std::set<Instruction*> &taintInstList);
    static void dumpTaintValueSet(std::set<Value*> &taintValueSet);
    static void checkLoadInst(Instruction *inst, 
                              std::vector<TaintArgInfo> &taintArgSet, 
                              std::vector<SharedTaint> &sharedSet, 
                              AliasAnalysis &AA, 
                              RelFlowSet &flowSet); 
    static void checkStoreInst(Instruction *inst, 
                               std::vector<TaintArgInfo> &taintArgSet, 
                               std::vector<SharedTaint> &sharedSet, 
                               AliasAnalysis &AA, 
                               RelFlowSet &flowSet); 
    static void checkAtomicInst(Instruction *inst, 
                                std::vector<TaintArgInfo> &taintArgSet, 
                                std::vector<SharedTaint> &sharedSet, 
                                AliasAnalysis &AA, 
                                RelFlowSet &flowSet); 
};
}
