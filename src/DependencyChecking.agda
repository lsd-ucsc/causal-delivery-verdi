open import Data.Nat as ℕ

module DependencyChecking (n : ℕ) (RawMsg : Set) where

open import Data.Maybe
open import Data.Bool
open import Data.Fin as Fin
open import Data.Product
open import Data.List as List
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Unit
open import Relation.Nullary using (Dec; yes; no)

open import Verdi

Node = Fin n

record MsgId : Set where
  field
    pid : Node
    ct  : ℕ

Deps : Set
Deps = List MsgId

record Msg : Set where
  field
    id  : MsgId
    deps : Deps
    raw : RawMsg

data Input : Set where
  send : (dst : Node) → (raw : RawMsg) → Input

data Output : Set where
  deliver : List RawMsg → Output -- sometimes we deliver 0 message
                                 -- messages in the list are ordered by their dependencies

record Process : Set where
  field
    id : Node
    deps : Deps
    msgCt : ℕ
    dq : List Msg

handleInput : Node → Process → Input → Process × Output × List (Packet Node Msg)
handleInput src p (send dst raw) = p′ , deliver [ raw ] ,  [ src ⇒ dst ⦂ msg ]
  where
    msgid = record { pid = Process.id p ; ct = Process.msgCt p }
    msg = record { id = msgid ; deps = Process.deps p ; raw = raw }
    p′ = record p { deps = msgid ∷ (Process.deps p) ; msgCt = (Process.msgCt p) ℕ.+ 1}

-- deliverable : (p : Process) → (m : Msg) → Dec (Msg.deps m ⊆ Process.deps p)
_==_ : MsgId → MsgId → Bool
deliverable : Process → Msg → Bool
deliverable p m = all (λ d → any (d ==_ ) (Process.deps p)) (Msg.deps m)

-- NOTE: Agda termination checker doesn't recoginize record update syntax
-- NOTE: This function may not return all deliverable messages, so needs to be called repeatedly until it returens an empty list
processDq : Process → Process × List Msg
processDq p@record { id = id ; deps = deps ; msgCt = msgCt ; dq = [] } = p , []
processDq p@record { id = id ; deps = deps ; msgCt = msgCt ; dq = (x ∷ xs) }
  = let p′ , msgs =  processDq record { id = id ; deps = deps ; msgCt = msgCt ; dq = xs } in
    if   deliverable p x
    then record p′ { deps = Msg.deps x ++ Process.deps p′} , x ∷ msgs
    else record p′ { dq = x ∷ Process.dq p′ } , msgs

handleMsg : Node → Process → Packet Node Msg → Process × Output × List (Packet Node Msg)
handleMsg dst p (_ ⇒ _ ⦂ msg) = p″ , deliver raws , []
  where
    p′ = record p { dq = msg ∷ Process.dq p }
    p″,msgs = processDq p′
    p″ = proj₁ p″,msgs
    raws = List.map Msg.raw (proj₂ p″,msgs)

DependencyChecking : App
DependencyChecking = record
                { Node = Node
                ; _≟_ = Fin._≟_
                ; State = λ _ → Process
                ; Msg = Msg
                ; Input = Input
                ; Output = Output
                ; initState = λ id → record { id = id ; deps = [] ; msgCt = 0 ; dq = [] }
                ; HandleInp = handleInput
                ; HandleMsg = handleMsg
                }
