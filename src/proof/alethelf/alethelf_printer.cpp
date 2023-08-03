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

#include "proof/alethelf/alethelf_printer.h"

#include <iostream>
#include <sstream>

#include "expr/node_algorithm.h"

namespace cvc5::internal {

namespace proof {

// This is some Lean stuff I need to update
void AletheLFPrinter::printAletheLFString(std::ostream& s, Node n)
{
  Kind k = n.getKind();
  if (k == kind::VARIABLE)
  {
    s << n.toString();
  }
  else
  {
    s << "(";
    printKind(s, k);
    s << " ";
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      printAletheLFString(s, n[i]);
      if (i != size - 1)
      {
        s << " ";
      };
    }
    s << ")";
  }
}

void AletheLFPrinter::printAletheLFType(std::ostream& s, Node n)
{
  // convert from node to AletheLF Type syntax:
  // products are curried
  // types are wrapped in "holds [_]"
  Kind k = n.getKind();
  switch (k)
  {
    case kind::VARIABLE: s << n.toString(); break;
    case kind::AND:
    {
      printAletheLFType(s, n[0]);
      s << " -> ";
      printAletheLFType(s, n[1]);
      break;
    }
    default:
      s << "thHolds ";
      printAletheLFString(s, n);
      break;
  }
}

void AletheLFPrinter::printAletheLFTypeToBottom(std::ostream& s, Node n)
{
  // print AletheLF type corresponding to proof of unsatisfiability
  printAletheLFType(s, n[0]);
  s << " -> holds []";
}

void AletheLFPrinter::printProof(std::ostream& out,
                                 std::shared_ptr<ProofNode> pfn,
                                 std::map<Node, std::string>& passumeMap)
{
  // print rule specific lean syntax, traversing children before parents in
  // ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  if (pfn->getRule() == PfRule::SCOPE)
  {
    // ?
  }
  else
  {
    for (const std::shared_ptr<ProofNode>& ch : children)
    {
      printProof(out, ch, passumeMap);
    }
  }
  switch (pfn->getRule())
  {
    default:
    {
      out << args;
      out << " ?\n";
      break;
    }
  }
}

void AletheLFPrinter::printSortsAndConstants(
    std::ostream& out,
    const std::vector<Node>& assertions,
    std::shared_ptr<ProofNode> pfn)
{
  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  std::vector<Node> iasserts;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(a);
  }
  int sortCount = 1;
  int symCount = 1;
  std::unordered_set<TypeNode> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isUninterpretedSort() && sts.find(st) == sts.end())
    {
      // declare a user defined sort, if that sort has not been encountered
      // before
      sts.insert(st);
      out << "def " << st << " := sort.atom " << sortCount << std::endl;
      sortCount += 1;
    }
    // declare a constant of a predefined sort
    out << "def " << s << " := const " << symCount << " " << st << std::endl;
    symCount += 1;
  }
}

void AletheLFPrinter::print(std::ostream& out,
                            const std::vector<Node>& assertions,
                            std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid AletheLF output from a ProofNode
  std::map<Node, std::string> passumeMap;
  const std::vector<Node>& args = pfn->getArguments();
  out << "open smt\n";
  out << "open smt.sort smt.term\n";
  printSortsAndConstants(out, assertions, pfn);
  out << "noncomputable theorem th0 : ";
  printAletheLFTypeToBottom(out, args[1]);
  out << " := \n";
  printProof(out, pfn, passumeMap);
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5::internal
