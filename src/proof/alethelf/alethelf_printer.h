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
 * The printer for the experimental AletheLF format.
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALETHELF_PROOF_PRINTER_H
#define CVC4__PROOF__ALETHELF_PROOF_PRINTER_H

#include <iostream>

#include "expr/node_algorithm.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"

namespace cvc5::internal {

namespace proof {

class AletheLFPrinter
{
 public:
  AletheLFPrinter();
  ~AletheLFPrinter() {}

  /**
   * Print the full proof of assertions => false by pfn.
   */
  static void print(std::ostream& out,
                    const std::vector<Node>& assertions,
                    std::shared_ptr<ProofNode> pfn);

 private:
  /**
   * The AletheLF calculus represents x = y as (mkEq x y) and
   *  x ∧ y as (mkAnd x y).
   * printKind cases on the kind of node, and prints the
   *  corresponding AletheLF command among mkEq, mkAnd, mkOr, mkNot, etc
   */
  static void printKind(std::ostream& s, Kind k);
  /**
   * Convert a node to a AletheLF term -- must start with mk_ and take children
   * as args Example: kind::AND (kind::EQUAL a b) c --> mkAnd (mkEq a b) c
   */
  static void printAletheLFString(std::ostream& s, Node n);
  /**
   * Convert from node to AletheLF type syntax
   */
  static void printAletheLFType(std::ostream& s, Node n);
  /**
   * Print AletheLF type corresponding to proof of unsatisfiability.
   * This method is a wrapper around printAletheLFType.
   *  The full proof node will always be a proof of unsatisfiability
   *  via resolution. So the type printed to AletheLF will always end
   *  in "-> holds []", which acts like a proof of contradiction, or false.
   */
  static void printAletheLFTypeToBottom(std::ostream& s, Node n);
  /**
   * Print user defined sorts and constants of those sorts
   */
  static void printSortsAndConstants(std::ostream& out,
                                     const std::vector<Node>& assertions,
                                     std::shared_ptr<ProofNode> pfn);

  /**
   * For each proof node, the final AletheLF output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the AletheLF proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
  static void printProof(std::ostream& out,
                         std::shared_ptr<ProofNode> pfn,
                         std::map<Node, std::string>& passumeMap);
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
