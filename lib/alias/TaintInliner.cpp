#include "TaintInliner.h"

using namespace taint;

char TaintInliner::ID = 0;

RegisterPass<TaintInliner> X("taint-inline", "Taint inliner pass");

Pass *llvm::createFunctionInliningPass() { 
  return new TaintInliner(); 
}

Pass *llvm::createFunctionInliningPass(int Threshold) {
  return new TaintInliner(Threshold);
}

// doInitialization - Initializes the vector of functions that have been
// annotated with the noinline attribute.
bool TaintInliner::doInitialization(CallGraph &CG) {
  return false;
}
