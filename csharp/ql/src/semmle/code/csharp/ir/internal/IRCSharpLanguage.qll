private import csharp as CSharp

class Function = CSharp::Callable;
class Location = CSharp::Location;
class AST = CSharp::Element;

class Type = CSharp::Type;
//REVIEW: This might not exist in the database. 
class UnknownType = CSharp::UnknownType;
class VoidType = CSharp::VoidType;
class IntegralType = CSharp::IntegralType;
class FloatingPointType = CSharp::FloatingPointType;

private newtype TClassDerivation = 
  // Note that this is the `Class` type exported from this module, not CSharp::Class.
  MkClassDerivation(Class base, Class derived) {
    derived.getABaseType() = base
  }

class ClassDerivation extends MkClassDerivation {
  Class baseClass;
  Class derivedClass;

  ClassDerivation() {
    this = MkClassDerivation(baseClass, derivedClass)
  }

  string toString() {
    result = "ClassDerivation"
  }

  final Class getBaseClass() {
    result = baseClass
  }

  final Class getDerivedClass() {
    result = derivedClass
  }

  final int getByteOffset() {
    // Inheritance never requires adjusting the `this` pointer in C#.
    result = 0
  }
}

class StringLiteral = CSharp::StringLiteral;

class Variable = CSharp::Variable;
class AutomaticVariable = CSharp::LocalScopeVariable;
class StaticVariable = CSharp::Variable;
class Parameter = CSharp::Parameter;
class Field = CSharp::Field;

// TODO: Remove necessity for these.
class Expr = CSharp::Expr;
class Class = CSharp::RefType;  // Used for inheritance conversions

string getIdentityString(Function func) {
  // REVIEW: Is this enough to make it unique?
//  result = func.getQualifiedName()
  result = func.getName()
}

predicate hasCaseEdge(string minValue, string maxValue) {
  // TODO: Need to handle `switch` statements that switch on an integer.
  none()
}

predicate hasPositionalArgIndex(int argIndex) {
  exists(CSharp::MethodCall call |
    exists(call.getArgument(argIndex))
  )
}

predicate hasAsmOperandIndex(int operandIndex) {
  none()
}

int getTypeSize(Type type) {
  // REVIEW: Is this complete?
  result = type.(CSharp::SimpleType).getSize() or
  result = getTypeSize(type.(CSharp::Enum).getUnderlyingType()) or
  // TODO: Generate a reasonable size
  type instanceof CSharp::Struct and result = 16 or
  type instanceof CSharp::RefType and result = getPointerSize() or
  type instanceof CSharp::PointerType and result = getPointerSize() or
  result = getTypeSize(type.(CSharp::TupleType).getUnderlyingType()) or
  // TODO: Add room for extra field
  result = getTypeSize(type.(CSharp::NullableType).getUnderlyingType()) or
  type instanceof CSharp::VoidType and result = 0
}

int getPointerSize() {
  // TODO: Deal with sizes in general
  result = 8
}

predicate isVariableAutomatic(Variable var) {
  var instanceof CSharp::LocalScopeVariable
}

string getStringLiteralText(StringLiteral s) {
  // REVIEW: Is this the right escaping?
  result = s.toString()
}

predicate hasPotentialLoop(Function f) {
  exists(CSharp::LoopStmt l | l.getEnclosingCallable() = f) or
  exists(CSharp::GotoStmt s | s.getEnclosingCallable() = f)
}

predicate hasGoto(Function f) {
  exists(CSharp::GotoStmt s | s.getEnclosingCallable() = f)
}