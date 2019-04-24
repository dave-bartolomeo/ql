import default
import semmle.code.cpp.ir.implementation.unaliased_ssa.internal.SSAConstruction
private import semmle.code.cpp.ir.internal.IntegerConstant as Ints

module Raw {
  import semmle.code.cpp.ir.implementation.raw.IR
  import semmle.code.cpp.ir.implementation.raw.gvn.ValueNumbering
  import semmle.code.cpp.ir.implementation.unaliased_ssa.internal.AliasAnalysis
  import semmle.code.cpp.ir.implementation.unaliased_ssa.internal.SimpleSSA

  string pointsToText(AddressOperand operand) {
    exists(IRVariable var, Ints::IntValue bitOffset |
      operandPointsToVariable(operand, var, bitOffset) and
      result = var.toString() + getBitOffsetString(bitOffset)
    ) or
    not operandPointsToVariable(operand, _, _) and result = "unknown" 
  }
}

module USSA {
  import semmle.code.cpp.ir.implementation.unaliased_ssa.IR
  import semmle.code.cpp.ir.implementation.unaliased_ssa.gvn.ValueNumbering
  import semmle.code.cpp.ir.implementation.aliased_ssa.internal.AliasAnalysis
  import semmle.code.cpp.ir.implementation.aliased_ssa.internal.AliasedSSA

  string regionText(AddressOperand operand) {
    exists(MemoryRegion region |
      region = getOperandMemoryRegion(operand) and
      result = region.getExampleInstruction().getOperationString()
    ) or
    not exists(getOperandMemoryRegion(operand)) and result = "unknown"
  }

  string baseOffsetText(AddressOperand operand) {
    exists(ValueNumber base, int bitOffset |
      operandBaseAndConstantOffset(operand, base, bitOffset) and
      result = base.getExampleInstruction().getOperationString() + getBitOffsetString(bitOffset)
    ) or
    not operandBaseAndConstantOffset(operand, _, _) and result = "??"
  }
}

from Raw::AddressOperand rawOperand, USSA::AddressOperand ussaOperand, string rawPointsTo,
  string ussaRegion, string ussaBaseOffset
where
  rawOperand.getUseInstruction() = getOldInstruction(ussaOperand.getUseInstruction()) and
  rawPointsTo = Raw::pointsToText(rawOperand) and
  ussaRegion = USSA::regionText(ussaOperand) and
  ussaBaseOffset = USSA::baseOffsetText(ussaOperand) and
  ussaRegion != "VariableAddress[i]" and
  ussaRegion != "VariableAddress[p]" and
  ussaRegion != "VariableAddress[q]"
select rawOperand.getUseInstruction().getLocation().toString(), rawOperand.getUseInstruction().getOperationString(),
  rawPointsTo, ussaRegion, ussaBaseOffset