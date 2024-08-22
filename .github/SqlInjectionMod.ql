/**
 * @name SQL query built from user-controlled sources
 * @description Building a SQL query from user-controlled sources is vulnerable to insertion of
 *              malicious SQL code by the user.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 8.8
 * @precision high
 * @id py/sql-injection
 * @tags security
 *       external/cwe/cwe-089
 */

import python
import semmle.python.security.dataflow.SqlInjectionQuery

module Flows = TaintTracking::Global<SqlInjectionConfigMod>;

private import semmle.python.Concepts
private import semmle.python.ApiGraphs

private module SqlInjectionConfigMod implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof Source }

  predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

  predicate isBarrier(DataFlow::Node node) { node instanceof Sanitizer }

  predicate isAdditionalFlowStep(DataFlow::Node a, DataFlow::Node b) {
    exists(File f | a.getLocation().getFile() = f and b.getLocation().getFile() = f and not f.inStdlib())
    and (
      exists(Call c | API::moduleImport("urllib").getMember("parse").getMember(["parse_qs", "unquote"]).getACall().asExpr() = c and
        c.getPositionalArg(0) = a.asExpr() and
        b.asExpr().getAFlowNode() = c.getAFlowNode()
      )
      or
      exists(Call c | API::moduleImport("re").getMember(["finditer", "findall"]).getACall().asExpr() = c and
        c.getPositionalArg(1) = a.asExpr() and
        b.asExpr().getAFlowNode() = c.getAFlowNode()
      )
      or
      exists(AssignStmt assign, Name use, Variable var |
        assign.getTarget(_) = a.asExpr()
        and use = b.asExpr()
        and assign.defines(var)
        and var.getAnAccess() = use
        and use.getId() = "query"
        and a != b
      )
    )
  }
}

// int explorationLimit() { result = 25 }
// module FlowsPartial = Flows::FlowExploration<explorationLimit/0>;
// import FlowsPartial::PartialPathGraph
// from FlowsPartial::PartialPathNode source, FlowsPartial::PartialPathNode sink
// where FlowsPartial::partialFlowRev(source, sink, _)
// and source.getNode().getLocation().getStartLine() = [248 .. 267]
// select source.getNode(), source, sink, "This node receives taint from $@.", source.getNode(),
//   "this source"
//where FlowsPartial::partialFlow(source, sink, _)
//and sink.getNode().getLocation().getStartLine() = [248 .. 267]
//select sink.getNode(), source, sink, "This node receives taint from $@.", source.getNode(),
//  "this source"

import Flows::PathGraph
from Flows::PathNode source, Flows::PathNode sink
where Flows::flowPath(source, sink)
select sink.getNode(), source, sink, "This node receives taint from $@.", source.getNode(),
  "this source"
