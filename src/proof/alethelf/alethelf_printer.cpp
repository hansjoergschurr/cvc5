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

#include <cctype>
#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "proof/proof_node_to_sexpr.h"

namespace cvc5::internal {

namespace proof {

std::string AletheLFPrinter::getRuleName(std::shared_ptr<ProofNode> pfn)
{
  std::string name = toString(pfn->getRule());
  std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) {
    return std::tolower(c);
  });
  return name;
}

void AletheLFPrinter::printProof(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    size_t& lastStep,
    std::map<std::shared_ptr<ProofNode>, size_t>& stepMap)
{
  if (pfn->getRule() == PfRule::SCOPE)
  {
    out << "; Oh no! it's a scope." << std::endl;
  }

  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  for (const std::shared_ptr<ProofNode>& ch : children)
  {
    printProof(out, ch, lastStep, stepMap);
  }

  if (pfn->getRule() == PfRule::SCOPE)
  {
    return;
  }

  lastStep += 1;
  out << "(step t" << lastStep << " " << pfn->getResult() << " :rule "
      << getRuleName(pfn);

  if (pfn->getChildren().size() == 0 && pfn->getArguments().size() > 0)
  {
    out << " :premises ()";
  }
  else if (pfn->getChildren().size() > 0)
  {
    bool first = true;
    for (std::shared_ptr<ProofNode> premise : pfn->getChildren())
    {
      if (first)
      {
        out << " :premises (";
        first = false;
      }
      else
      {
        out << " ";
      }
      out << "t" << stepMap[premise];
    }
    out << ")";
  }
  if (pfn->getArguments().size() > 0)
  {
    // Hack to get the arguments converted into something useful
    ProofNodeToSExpr sexpPrinter;
    Node sexp = sexpPrinter.convertToSExpr(pfn.get(), false);
    bool first = true;
    for (Node arg : sexp[sexp.getNumChildren() - 1])
    {
      if (first)
      {
        out << " :args (";
        first = false;
      }
      else
      {
        out << " ";
      }
      out << arg;
    }
    out << ")";
  }
  out << ")" << std::endl;

  stepMap[pfn] = lastStep;
}

void AletheLFPrinter::printSortsAndConstants(std::ostream& out,
                                             std::shared_ptr<ProofNode> pfn)
{
  // TODO: this does something, I don't know what

  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  std::vector<Node> iasserts;

  const std::vector<Node>& assertions = pfn->getArguments();
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

void AletheLFPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid AletheLF output from a ProofNode
  std::map<std::shared_ptr<ProofNode>, size_t> stepMap;
  size_t lastStep = 0;

  out << "(import \"../proof/rules/Boolean.smt2\")\n";
  printSortsAndConstants(out, pfn);
  printProof(out, pfn, lastStep, stepMap);
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5::internal
