/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumeration of AletheLF specific proof rules.  These are mostly variants of
 * standard cvc5 rules that are slight adapted to the limits of AletheLF.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHELF__ALETHELF_PROOF_RULE_H
#define CVC5__PROOF__ALETHELF__ALETHELF_PROOF_RULE_H

#include <iostream>

#include "expr/node.h"

namespace cvc5::internal {

namespace proof {

enum class AletheLFRule : uint32_t
{
  AND_INTRO_NARY,
  CHAIN_RESOLUTION,
  CONG,
  // ======== undefined
  // Used in case that a step in the proof rule could not be translated.
  UNDEFINED
};

/**
 * Converts an Alethe proof rule to a string.
 *
 * @param id The Alethe proof rule
 * @return The name of the Alethe proof rule
 */
const char* aletheLFRuleToString(AletheLFRule id);

/**
 * Writes an AletheLF proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The AletheLF proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, AletheLFRule id);

/** Convert a node holding an id to the corresponding AletheLFRule */
AletheLFRule getAletheLFRule(Node n);

}  // namespace proof

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHELF__ALETHELF_PROOF_RULE_H */
