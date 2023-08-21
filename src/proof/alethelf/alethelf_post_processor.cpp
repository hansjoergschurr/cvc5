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
  switch (pn->getRule())
  {
    case PfRule::CHAIN_RESOLUTION:
      return true;
    case PfRule::CONG: return true;
    default:
      return false;
  }
}

bool AletheLFProofPostprocessCallback::addAletheLFStep(
    AletheLFRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> newArgs{NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(rule)))};
  for (const Node& arg : args)
  {
    newArgs.push_back(arg);
  }
  Trace("alethe-proof") << "... add alethelf step " << conclusion << " " << rule
                        << " " << children << " / " << newArgs << std::endl;
  return cdp.addStep(conclusion, PfRule::ALETHELF_RULE, children, newArgs);
}

bool AletheLFProofPostprocessCallback::update(Node res,
                                              PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args,
                                              CDProof* cdp,
                                              bool& continueUpdate)
{
  Trace("alethelf-proof") << "...AletheLF pre-update " << res << " " << id
                          << " " << children << " / " << args << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  switch (id)
  {
    case PfRule::CHAIN_RESOLUTION:
    {
      // create and_intro for each child
      // create big conjunction for args
      Assert(children.size() >= 2);
      Node conj = nm->mkNode(kind::AND, children);
      Node argsList = nm->mkNode(kind::AND, args);
      // This AND_INTRO will also be preprocessed to multiple AND_INTRO_NARY
      cdp->addStep(conj, PfRule::AND_INTRO, children, std::vector<Node>());
      return addAletheLFStep(
          AletheLFRule::CHAIN_RESOLUTION, res, {conj}, {argsList}, *cdp);
    }
    case PfRule::CONG:
    {
      Node start;

      // (HO_APPLY (f) l1
      if (args[0].getKind() == kind::APPLY_UF)
      {
        arg = args[1];
      }
      else
      {
        arg = args[0];
      }

      Node partialCong = arg;
      for (const Node& eq : children)
      {
        partialCong = nm->mkNode(Kind::APPLY_UF, eq[1]);
      }
      Node conj = nm->mkNode(kind::AND, children);
      Node argsList = nm->mkNode(kind::AND, args);

      addAletheLFStep(AletheLFRule::CONG, res, {conj}, {arg}, *cdp);
      cdp->addStep(conj, PfRule::AND_INTRO, children, std::vector<Node>());
    }
    default:
      return false;
  }
}

void AletheLFProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5::internal
