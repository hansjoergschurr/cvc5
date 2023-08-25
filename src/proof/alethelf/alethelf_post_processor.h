/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The post processor for the experimental AletheLF format.
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALETHELF_POST_PROCESSOR_H
#define CVC4__PROOF__ALETHELF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "proof/alethelf/alethelf_proof_rule.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_updater.h"

namespace cvc5::internal {

namespace proof {

/**
 * A callback class used by the AletheLF convereter for post-processing proof
 * nodes by replacing internal rules by the rules in the AletheLF calculus.
 */
class AletheLFProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  AletheLFProofPostprocessCallback(ProofNodeManager* pnm);
  /**
   * Initialize, called once for each new ProofNode to process. This
   * initializes static information to be used by successive calls to update.
   */
  void initializeUpdate();

  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The proof checker is used to generate conclusions from local
   * proof steps. This is currently only used in the resolution rule.
   */
  ProofChecker* d_pc;

  bool addAletheLFStep(AletheLFRule rule,
                       Node conclusion,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args,
                       CDProof& cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the AletheLF calculus.
 */
class AletheLFProofPostprocess : protected EnvObj
{
 public:
  AletheLFProofPostprocess(Env& env);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<AletheLFProofPostprocessCallback> d_cb;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
