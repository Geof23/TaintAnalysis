#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "TaintAnalysis.h"
#include <iostream>
#include <fstream>

namespace runtime {
  extern cl::opt<bool> Verbose;
}

using namespace taint;
using namespace runtime;

static bool isTwoInstIdentical(Instruction *inst1, 
                               Instruction *inst2) {
  std::string func1Name = inst1->getParent()->getParent()->getName().str();
  std::string func2Name = inst2->getParent()->getParent()->getName().str();

  BasicBlock *bb1 = inst1->getParent();
  BasicBlock *bb2 = inst2->getParent();

  return func1Name.compare(func2Name) == 0
           && bb1 == bb2
             && inst1->isIdenticalTo(inst2);
}

static void annotateFunctionIR(LLVMContext &glContext, 
                               Function *f, 
                               CFGNode *node) {
  bool instFound = false;

  for (Function::iterator fi = f->begin(); fi != f->end(); fi++) {
    for (BasicBlock::iterator bi = fi->begin(); bi != fi->end(); bi++) {
      if (isTwoInstIdentical(bi, node->inst)) {
        // Value *CI = MDString::get(glContext, "brprop");
        // ArrayRef<Value*> temp = ArrayRef<Value*>(CI);
        MDNode *mdNode = MDNode::get(bi->getContext(), MDString::get(glContext, "brprop"));
	// MDNode *mdNode = MDNode::get(bi->getContext(), temp);

        std::string str = "br";
        for (unsigned i = 0; i < node->cfgInstSet.size(); i++) {
          if (node->cfgInstSet[i].explore) {
            if (node->cfgInstSet[i].global)
              str += "-G";
            else if (node->cfgInstSet[i].shared)
              str += "-S";
          } else {
            str += "-S";
          }
        }

        if (node->causeIteration) {
          str += "-ite";
        }

        if (Verbose > 0) {
          std::cout << "The br inst: " << std::endl;
          node->inst->dump();
          std::cout << "Metadata: " << str << std::endl;
        }
        bi->setMetadata(str, mdNode);
        instFound = true;
        break;
      }
    }
    if (instFound) break;
  }
}

void CFGTree::exploreCFGTreeToAnnotate(LLVMContext &glContext, 
                                       Function *f, 
                                       CFGNode *node) {
  if (node) {
    //std::cout << "node inst: " << node->causeIteration << std::endl;
    //node->inst->dump();
    annotateFunctionIR(glContext, f, node);
    for (unsigned i = 0; i < node->cfgNodes.size(); i++) {
      exploreCFGTreeToAnnotate(glContext, f, node->cfgNodes[i]);
    }
    exploreCFGTreeToAnnotate(glContext, f, node->successor);
  }
}

