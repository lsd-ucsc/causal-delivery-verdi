open import Data.Nat as ℕ

module CausalTracking (n : ℕ) (RawMsg : Set) where

open import Data.Fin as Fin
open import Data.Product
open import Data.List
open import Data.Unit

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

record Process : Set where
  field
    id : Node
    deps : Deps
    msgCt : ℕ

handleInput : Node → Process → Input → Process × ⊤ × List (Packet Node Msg)
handleInput src p (send dst raw) = p′ , tt , pkt ∷ []
  where
    msgid = record { pid = Process.id p ; ct = Process.msgCt p }
    msg = record { id = msgid ; deps = Process.deps p ; raw = raw }
    pkt = record { src = src ; dst = dst ; msg = msg }
    p′ = record p { deps = msgid ∷ (Process.deps p) ; msgCt = (Process.msgCt p) ℕ.+ 1}

causalTrack : App
causalTrack = record
                { Node = Node
                ; _≟_ = Fin._≟_
                ; State = λ _ → Process
                ; Msg = Msg
                ; Input = Input
                ; Output = ⊤
                ; initState = λ id → record { id = id ; deps = [] ; msgCt = 0 }
                ; HandleInp = handleInput
                ; HandleMsg = {!!}
                }
