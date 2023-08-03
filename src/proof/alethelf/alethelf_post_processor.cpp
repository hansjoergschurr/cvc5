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

#include "proof/alethelf/alethelf_post_processor.h"

#include "proof/lazy_proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "util/rational.h"

namespace cvc5::internal {

namespace proof {

AletheLFProofPostprocessCallback::AletheLFProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker())
{
}

AletheLFProofPostprocess::AletheLFProofPostprocess(Env& env)
    : EnvObj(env),
      d_cb(new proof::AletheLFProofPostprocessCallback(
          env.getProofNodeManager()))
{
}

bool AletheLFProofPostprocessCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  return pn->getRule() != PfRule::LEAN_RULE;
};

bool AletheLFProofPostprocessCallback::update(Node res,
                                              PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args,
                                              CDProof* cdp,
                                              bool& continueUpdate)
{
  return false;
}

void AletheLFProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5::internal
