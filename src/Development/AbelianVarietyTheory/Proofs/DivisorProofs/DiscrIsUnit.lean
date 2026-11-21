module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE

@[expose] public section

open IsLocalRing

open TensorProduct

namespace GlobalTheory.EtaleCoker

theorem discr_isUnit (S A : Type) [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    [Algebra.Etale S A] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S A) :
    IsUnit (Algebra.discr S b) := by
  classical
  let K := ResidueField S
  let L := AlgebraicClosure K
  let : Algebra S L := Algebra.compHom L (residue S)
  let B := L ⊗[S] A
  let c := Algebra.TensorProduct.basis L b
  have : Module.Finite L B := Module.Finite.of_basis c
  have : IsArtinianRing B := isArtinian_of_tower L inferInstance
  let : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L B
  have trace_pi (z : PrimeSpectrum B → L) : Algebra.trace L (PrimeSpectrum B → L) z = ∑ i, z i := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basisFun L (PrimeSpectrum B)), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  have hLeft : (Algebra.traceForm L (PrimeSpectrum B → L)).SeparatingLeft := by
    intro x hx
    funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h
  have hdisc : Algebra.discr L c ≠ 0 := by
    rw [Algebra.discr_eq_discr_of_algEquiv c e]
    change Algebra.discr L (c.map e.toLinearEquiv) ≠ 0
    rw [Algebra.discr_def, Algebra.traceMatrix_of_basis,
      ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
    exact ⟨hLeft, fun x hx => hLeft x fun y => by
      simpa only [Algebra.traceForm_apply, mul_comm] using hx y⟩
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have trace_baseChange (a : A) :
      Algebra.trace L (L ⊗[S] A) (1 ⊗ₜ[S] a) = algebraMap S L (Algebra.trace S A a) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]
  have hbase : Algebra.discr L c = algebraMap S L (Algebra.discr S b) := by
    rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
    congr 1
    ext i j
    simp only [c, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact trace_baseChange (b i * b j)
  rw [hbase] at hdisc
  apply (residue_ne_zero_iff_isUnit _).mp
  intro h
  apply hdisc
  change algebraMap K L (residue S (Algebra.discr S b)) = 0
  rw [h, map_zero]

end GlobalTheory.EtaleCoker
