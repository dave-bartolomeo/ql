private import cpp
private import IntegerConstant
private import IRUtilities
private import semmle.code.cpp.ir.implementation.raw.internal.IRConstruction as IRConstruction

private int getPointerSize() {
  result = max(NullPointerType nullType | any() | nullType.getSize())
}

private class BlobType extends Type {
  BlobType() {
    exists(this.(Class).getSize()) or  // Only include complete classes
    this instanceof ArrayType or
    this instanceof PointerToMemberType or
    this instanceof GNUVectorType
  }
}

private predicate isRepresentableType(Type type) {
  exists(Type unspecifiedType |
    unspecifiedType = type.getUnspecifiedType() and
    (
      unspecifiedType instanceof VoidType or
      unspecifiedType instanceof IntegralOrEnumType or  // Includes `bool`
      unspecifiedType instanceof FloatingPointType or
      unspecifiedType instanceof PointerType or
      unspecifiedType instanceof ReferenceType or
      unspecifiedType instanceof FunctionPointerIshType or
      unspecifiedType instanceof ErroneousType or
      unspecifiedType instanceof BlobType or
      unspecifiedType instanceof RoutineType
    )
  )
}

private newtype TIRType =
  TIRPRValueType(Type type) {
    isRepresentableType(type) and
    not type.getUnspecifiedType() instanceof RoutineType  // No such thing as a function prvalue
  } or
  TIRFunctionGLValueType() or
  TIRGLValueAddressType(Type type) {
    isRepresentableType(type)
  } or
  TIRUnknownBlobType(int byteSize) {
    IRConstruction::needsUnknownBlobType(byteSize)
  } or
  TIRUnknownType()

class IRType extends TIRType {
  string toString() {
    result = "???"
  }

  int getByteSize() {
    none()
  }

  predicate hasType(Type type, boolean isGLValue) {
    none()
  }
}

private class IRWrappedType extends IRType {
  Type ctype;

  IRWrappedType() {
    this = TIRPRValueType(ctype) or
    this = TIRGLValueAddressType(ctype)
  }
}

private class IRPRValueType extends IRWrappedType, TIRPRValueType {
  override final string toString() {
    result = ctype.getUnspecifiedType().toString()
  }

  override final int getByteSize() {
    result = ctype.getSize()
  }

  override final predicate hasType(Type type, boolean isGLValue) {
    type = ctype and
    isGLValue = false
  }
}

class IRErrorType extends IRPRValueType {
  IRErrorType() {
    ctype.getUnspecifiedType() instanceof ErroneousType
  }
}

class IRVoidType extends IRPRValueType {
  IRVoidType() {
    ctype.getUnspecifiedType() instanceof VoidType
  }
}

class IRNumericType extends IRPRValueType {
  IRNumericType() {
    exists(Type unspecifiedType |
      unspecifiedType = ctype.getUnspecifiedType() and
      (
        unspecifiedType instanceof FloatingPointType or
        unspecifiedType instanceof IntegralOrEnumType and not unspecifiedType instanceof BoolType
      )
    )
  }
}

class IRIntegerType extends IRNumericType {
  IRIntegerType() {
    ctype.getUnspecifiedType() instanceof IntegralOrEnumType
  }
}

private predicate isSignedInteger(Type type) {
  exists(IntegralType integralType |
    integralType = type.getUnspecifiedType() and
    integralType.isSigned()
  ) or
  exists(Enum enumType |
    enumType = type.getUnspecifiedType() and
    (
      enumType.getExplicitUnderlyingType().getUnspecifiedType().(IntegralType).isSigned() or
      not exists(enumType.getExplicitUnderlyingType())  // Assume signed.
    )
  )
}

class IRSignedIntegerType extends IRIntegerType {
  IRSignedIntegerType() {
    isSignedInteger(ctype)
  }
}

class IRUnsignedIntegerType extends IRIntegerType {
  IRUnsignedIntegerType() {
    not isSignedInteger(ctype)
  }
}

class IRFloatingPointType extends IRNumericType {
  IRFloatingPointType() {
    ctype.getUnspecifiedType() instanceof FloatingPointType
  }
}

class IRBooleanType extends IRPRValueType {
  IRBooleanType() {
    ctype.getUnspecifiedType() instanceof BoolType
  }
}

class IRBlobType extends IRType {
  int byteSize;

  IRBlobType() {
    exists(Type type |
      this = TIRPRValueType(type) and
      byteSize = type.getUnspecifiedType().(BlobType).getSize()
    ) or
    this = TIRUnknownBlobType(byteSize)
  }
}

private class IRWrappedBlobType extends IRBlobType, IRPRValueType {
}

private class IRUnknownBlobType extends IRBlobType, TIRUnknownBlobType {
  override final string toString() {
    result = "unknown[" + byteSize.toString() + "]"
  }

  override final int getByteSize() {
    result = byteSize
  }
}

private predicate isPointerIshType(Type type) {
  exists(Type unspecifiedType |
    unspecifiedType = type.getUnspecifiedType() and
    (
      unspecifiedType instanceof PointerType or
      unspecifiedType instanceof ReferenceType
    )
  )
}

class IRAddressType extends IRWrappedType {
  IRAddressType() {
    this = TIRGLValueAddressType(ctype) or
    isPointerIshType(ctype)
  }
}

private class IRPRValueAddressType extends IRAddressType, IRPRValueType {
}

private class IRGLValueAddressType extends IRAddressType, TIRGLValueAddressType {
  override final string toString() {
    result = "glval<" + ctype.getUnspecifiedType().toString() + ">"
  }
  
  override final int getByteSize() {
    result = getPointerSize()
  }

  override final predicate hasType(Type type, boolean isGLValue) {
    type = ctype and
    isGLValue = true
  }
}

class IRFunctionAddressType extends IRType {
  IRFunctionAddressType() {
    exists(Type ctype |
      this = TIRPRValueType(ctype) and
      ctype.getUnspecifiedType() instanceof FunctionPointerIshType
    ) or
    this = TIRFunctionGLValueType()
  }
}

private class IRFunctionPointerishType extends IRFunctionAddressType, IRPRValueType {
}

private class IRFunctionGLValueType extends IRFunctionAddressType, TIRFunctionGLValueType {
  override final string toString() {
    result = "glval<unknown>"
  }

  override final int getByteSize() {
    result = getPointerSize()
  }
}

class IRUnknownType extends IRType, TIRUnknownType {
  override final string toString() {
    result = "unknown"
  }
}

IRUnknownType getUnknownType() {
  any()
}

IRVoidType getVoidType() {
  exists(VoidType voidType |
    result.hasType(voidType, false)
  )
}

IRType getIRTypeForExpr(Expr expr) {
  exists(boolean isGLValue |
    (
      if expr.isGLValueCategory() then 
        isGLValue = true
      else
        isGLValue = false
    ) and
    result.hasType(expr.getType(), isGLValue)
  )
}

IRType getIRTypeForPRValue(Type type) {
  result.hasType(type, false)
}

IRAddressType getIRTypeForGLValue(Type type) {
  result.hasType(type, true)
}

IRSignedIntegerType getIntType() {
  exists(IntType type |
    type.isImplicitlySigned() and
    result.hasType(type, false)
  )
}

IRBooleanType getBoolType() {
  exists(BoolType type |
    result.hasType(type, false)
  )
}

IRFunctionGLValueType getFunctionGLValueType() {
  any()
}

IRUnknownBlobType getUnknownBlobType(int byteSize) {
  result.getByteSize() = byteSize
}
