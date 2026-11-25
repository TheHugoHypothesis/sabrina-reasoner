import Init.Data.List.Lemmas

/-! Typed logical syntax for OWL 2 Direct Semantics. Boolean lists have binary
forms and list constructors below. Data ranges have the arity of the standard
datatype map, namely one. An ontology is supplied as an axiom closure. -/

namespace Sabrina.OWL2

abbrev IRI := String

def thing : IRI := "http://www.w3.org/2002/07/owl#Thing"
def nothing : IRI := "http://www.w3.org/2002/07/owl#Nothing"
def topObjectProperty : IRI := "http://www.w3.org/2002/07/owl#topObjectProperty"
def bottomObjectProperty : IRI := "http://www.w3.org/2002/07/owl#bottomObjectProperty"
def topDataProperty : IRI := "http://www.w3.org/2002/07/owl#topDataProperty"
def bottomDataProperty : IRI := "http://www.w3.org/2002/07/owl#bottomDataProperty"
def literalDatatype : IRI := "http://www.w3.org/2000/01/rdf-schema#Literal"

inductive Individual where
  | named (iri : IRI)
  | anonymous (document localId : String)
  deriving DecidableEq, Repr

inductive ObjectProperty where
  | named (iri : IRI)
  | inverse (iri : IRI)
  deriving DecidableEq, Repr

def ObjectProperty.converse : ObjectProperty → ObjectProperty
  | .named r => .inverse r
  | .inverse r => .named r

structure Literal where
  lexical : String
  datatype : IRI
  deriving DecidableEq, Repr

structure Facet where
  name : IRI
  bound : Literal
  deriving DecidableEq, Repr

inductive DataRange where
  | datatype (iri : IRI)
  | complement (body : DataRange)
  | intersection (a b : DataRange)
  | union (a b : DataRange)
  | oneOf (literals : List Literal)
  | restriction (datatype : IRI) (facets : List Facet)
  deriving DecidableEq, Repr

def DataRange.intersect (ranges : List DataRange) : DataRange :=
  ranges.foldr .intersection (.datatype literalDatatype)

def DataRange.unite (ranges : List DataRange) : DataRange :=
  ranges.foldr .union (.complement (.datatype literalDatatype))

inductive ClassExpr where
  | named (iri : IRI)
  | complement (body : ClassExpr)
  | intersection (a b : ClassExpr)
  | union (a b : ClassExpr)
  | oneOf (individuals : List Individual)
  | objectSome (role : ObjectProperty) (filler : ClassExpr)
  | objectAll (role : ObjectProperty) (filler : ClassExpr)
  | objectValue (role : ObjectProperty) (value : Individual)
  | objectSelf (role : ObjectProperty)
  | objectMin (count : Nat) (role : ObjectProperty) (filler : ClassExpr)
  | objectMax (count : Nat) (role : ObjectProperty) (filler : ClassExpr)
  | objectExact (count : Nat) (role : ObjectProperty) (filler : ClassExpr)
  | dataSome (role : IRI) (range : DataRange)
  | dataAll (role : IRI) (range : DataRange)
  | dataValue (role : IRI) (value : Literal)
  | dataMin (count : Nat) (role : IRI) (range : DataRange)
  | dataMax (count : Nat) (role : IRI) (range : DataRange)
  | dataExact (count : Nat) (role : IRI) (range : DataRange)
  deriving DecidableEq, Repr

def ClassExpr.intersect (classes : List ClassExpr) : ClassExpr :=
  classes.foldr .intersection (.named thing)

def ClassExpr.unite (classes : List ClassExpr) : ClassExpr :=
  classes.foldr .union (.named nothing)

inductive Axiom where
  | subClassOf (sub sup : ClassExpr)
  | equivalentClasses (classes : List ClassExpr)
  | disjointClasses (classes : List ClassExpr)
  | disjointUnion (head : IRI) (classes : List ClassExpr)
  | subObjectProperty (sub sup : ObjectProperty)
  | subObjectPropertyChain (body : List ObjectProperty) (sup : ObjectProperty)
  | equivalentObjectProperties (roles : List ObjectProperty)
  | disjointObjectProperties (roles : List ObjectProperty)
  | inverseObjectProperties (r s : ObjectProperty)
  | objectPropertyDomain (role : ObjectProperty) (domain : ClassExpr)
  | objectPropertyRange (role : ObjectProperty) (range : ClassExpr)
  | functionalObjectProperty (role : ObjectProperty)
  | inverseFunctionalObjectProperty (role : ObjectProperty)
  | reflexiveObjectProperty (role : ObjectProperty)
  | irreflexiveObjectProperty (role : ObjectProperty)
  | symmetricObjectProperty (role : ObjectProperty)
  | asymmetricObjectProperty (role : ObjectProperty)
  | transitiveObjectProperty (role : ObjectProperty)
  | subDataProperty (sub sup : IRI)
  | equivalentDataProperties (roles : List IRI)
  | disjointDataProperties (roles : List IRI)
  | dataPropertyDomain (role : IRI) (domain : ClassExpr)
  | dataPropertyRange (role : IRI) (range : DataRange)
  | functionalDataProperty (role : IRI)
  | datatypeDefinition (datatype : IRI) (range : DataRange)
  | hasKey (domain : ClassExpr) (objectRoles : List ObjectProperty) (dataRoles : List IRI)
  | sameIndividuals (individuals : List Individual)
  | differentIndividuals (individuals : List Individual)
  | classAssertion (c : ClassExpr) (i : Individual)
  | objectAssertion (role : ObjectProperty) (subject value : Individual)
  | negativeObjectAssertion (role : ObjectProperty) (subject value : Individual)
  | dataAssertion (role : IRI) (subject : Individual) (value : Literal)
  | negativeDataAssertion (role : IRI) (subject : Individual) (value : Literal)
  deriving DecidableEq, Repr

abbrev Ontology := List Axiom

end Sabrina.OWL2
