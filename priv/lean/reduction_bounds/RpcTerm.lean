namespace ReductionBounds.RpcTerm

inductive Term where
  | atom (value : String)
  | integer (value : Int)
  | binary (value : List Nat)
  | ref (value : Nat)
  | pid (value : Nat)
  | nil
  | cons (v0 : Term) (v1 : Term)
  | tuple2 (v0 : Term) (v1 : Term)
  | tuple3 (v0 : Term) (v1 : Term) (v2 : Term)
  | tuple5 (v0 : Term) (v1 : Term) (v2 : Term) (v3 : Term) (v4 : Term)
  deriving DecidableEq

structure Size where
  nodes : Nat
  bytes : Nat
  bits : Nat
  deriving DecidableEq

def join (a b : Size) : Size := ⟨a.nodes + b.nodes, a.bytes + b.bytes, max a.bits b.bits⟩

def measure : Term → Size
  | .integer n => ⟨1, 0, if n == 0 then 0 else n.natAbs.log2 + 1⟩
  | .binary bs => ⟨1, bs.length, 0⟩
  | .cons v0 v1 => join (join (⟨1, 0, 0⟩) (measure v0)) (measure v1)
  | .tuple2 v0 v1 => join (join (⟨1, 0, 0⟩) (measure v0)) (measure v1)
  | .tuple3 v0 v1 v2 => join (join (join (⟨1, 0, 0⟩) (measure v0)) (measure v1)) (measure v2)
  | .tuple5 v0 v1 v2 v3 v4 => join (join (join (join (join (⟨1, 0, 0⟩) (measure v0)) (measure v1)) (measure v2)) (measure v3)) (measure v4)
  | _ => ⟨1, 0, 0⟩

def wellFormed : Term → Bool
  | .binary bs => bs.all (· < 256)
  | .cons v0 v1 => wellFormed v0 && wellFormed v1
  | .tuple2 v0 v1 => wellFormed v0 && wellFormed v1
  | .tuple3 v0 v1 v2 => wellFormed v0 && wellFormed v1 && wellFormed v2
  | .tuple5 v0 v1 v2 v3 v4 => wellFormed v0 && wellFormed v1 && wellFormed v2 && wellFormed v3 && wellFormed v4
  | _ => true

def within (actual cap : Size) : Bool :=
  actual.nodes <= cap.nodes && actual.bytes <= cap.bytes && actual.bits <= cap.bits

def child : Term → Nat → Option Term
  | .cons v0 _, 0 => some v0
  | .cons _ v1, 1 => some v1
  | .tuple2 v0 _, 0 => some v0
  | .tuple2 _ v1, 1 => some v1
  | .tuple3 v0 _ _, 0 => some v0
  | .tuple3 _ v1 _, 1 => some v1
  | .tuple3 _ _ v2, 2 => some v2
  | .tuple5 v0 _ _ _ _, 0 => some v0
  | .tuple5 _ v1 _ _ _, 1 => some v1
  | .tuple5 _ _ v2 _ _, 2 => some v2
  | .tuple5 _ _ _ v3 _, 3 => some v3
  | .tuple5 _ _ _ _ v4, 4 => some v4
  | _, _ => none

def atPath (term : Term) : List Nat → Option Term
  | [] => some term
  | i :: rest => (child term i).bind (fun next => atPath next rest)

end ReductionBounds.RpcTerm
