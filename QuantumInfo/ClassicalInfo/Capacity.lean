/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Entropy
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Fin
public import Mathlib.Data.Fintype.Fin

@[expose] public section

--Classical capacity
-- * Define "code"
-- * Define (Shannon) capacity of a (iid, memoryless) channel
-- * Prove Shannon's capacity theorems

variable (A I O : Type*)

private lemma blockIndexLt (len block_in : ℕ) (hmod : len % block_in = 0)
    (i : Fin (len / block_in)) (j : Fin block_in) :
    i.1 * block_in + j.1 < len := by
  have hlen : block_in * (len / block_in) = len := by
    simpa [hmod] using (Nat.mod_add_div len block_in)
  have hi : i.1 + 1 ≤ len / block_in := Nat.succ_le_of_lt i.2
  have hmul : (i.1 + 1) * block_in ≤ len := by
    calc
      (i.1 + 1) * block_in ≤ (len / block_in) * block_in := Nat.mul_le_mul_right _ hi
      _ = len := by simpa [Nat.mul_comm] using hlen
  calc
    i.1 * block_in + j.1 < i.1 * block_in + block_in := Nat.add_lt_add_left j.2 _
    _ = (i.1 + 1) * block_in := by rw [Nat.succ_mul]
    _ ≤ len := hmul

private def mapBlocks {α β : Type*} (block_in block_out : ℕ)
    (f : (Fin block_in → α) → (Fin block_out → β)) (xs : List α) : List β :=
  if hmod : xs.length % block_in = 0 then
    let block : Fin (xs.length / block_in) → List β := fun i =>
      List.ofFn <| f fun j =>
        xs[i.1 * block_in + j.1]'(blockIndexLt xs.length block_in hmod i j)
    List.flatten <| List.ofFn block
  else
    []

private theorem mapBlocks_length {α β : Type*} (block_in block_out : ℕ)
    (f : (Fin block_in → α) → (Fin block_out → β)) (xs : List α) :
    (mapBlocks block_in block_out f xs).length =
      if xs.length % block_in = 0 then (xs.length / block_in) * block_out else 0 := by
  by_cases hmod : xs.length % block_in = 0
  · simp [mapBlocks, hmod, List.length_flatten]
    let block : Fin (xs.length / block_in) → List β := fun i =>
      List.ofFn <| f fun j =>
        xs[i.1 * block_in + j.1]'(blockIndexLt xs.length block_in hmod i j)
    have hf : List.length ∘ block = fun _ => block_out := by
      funext i
      simp [block]
    rw [show List.ofFn (List.length ∘ block) = List.ofFn (fun _ : Fin (xs.length / block_in) => block_out) by rw [hf]]
    rw [List.ofFn_const, List.sum_replicate, nsmul_eq_mul]
    simp
  · simp [mapBlocks, hmod]

/-- Here we define a *Code* by an encdoder and a decoder. The encoder is a function that takes
 strings (`List`s) of any length over an alphabet `A`, and returns strings over `I`;
 the decoder takes `O` and gives back strings over `A`. The idea is that a channel
 would map from strings of `I` to `O`. Important special cases are where `I=O` (the channel doesn't
 change the symbol set), and `FixedLengthCode` where the output lengths only depend on input
 lengths. -/
structure Code where
  encoder : List A → List I
  decoder : List O → List A

/-- A `FixedLengthCode` is a `Code` whose output lengths don't depend on the input content, only
 the input length. -/
structure FixedLengthCode extends Code A I O where
  enc_length : ℕ → ℕ
  enc_maps_length : ∀ as, (encoder as).length = enc_length (as.length)
  dec_length : ℕ → ℕ
  dec_maps_length : ∀ is, (decoder is).length = dec_length (is.length)

/-- A `BlockCode` is a `FixedLengthCode` that (1) maps symbols in discrete blocks of fixed length,
 (2) the encoded alphabet `I` has a canonical injection into `O`, and (3) has encoder and decoders
 that are inverses of each other. This is well-suited to describing noise and erasure channels. If
 the channel merely "corrupts" the data then this `O = I`; the erasure channel might for instance
 take `O = I ⊕ Unit` or `Option I`.

 We define the behavior of a block code to "fail" if the input is not a multiple of the block size,
 by having it return an empty list. -/
structure BlockCode (io : I → O) extends FixedLengthCode A I O where
  block_in : ℕ
  block_out : ℕ
  block_enc : (Fin block_in → A) → (Fin block_out → I)
  block_dec : (Fin block_out → O) → (Fin block_in → A)
  block_enc_dec_inv : ∀ as, block_dec (io ∘ (block_enc as)) = as
  enc_length na := if na % block_in != 0 then 0 else (na / block_in) * block_out
  dec_length no := if no % block_out != 0 then 0 else (no / block_out) * block_in
  encoder := mapBlocks block_in block_out block_enc
  decoder := mapBlocks block_out block_in block_dec
  enc_maps_length := by
    intro as
    by_cases hmod : as.length % block_in = 0
    · simpa [mapBlocks_length, hmod]
    · simpa [mapBlocks_length, hmod]
  dec_maps_length := by
    intro os
    by_cases hmod : os.length % block_out = 0
    · simpa [mapBlocks_length, hmod]
    · simpa [mapBlocks_length, hmod]
