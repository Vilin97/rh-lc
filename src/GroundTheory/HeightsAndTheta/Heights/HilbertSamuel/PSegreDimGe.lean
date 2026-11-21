module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreDimGe
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Cardinal

noncomputable section

theorem SegreDimGe.proof : SegreDimGe.Statement := by
  intro F _ K _ _ _ ι _ q e hq hdim
  have := hq.isPrime
  let π : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι →ₐ[F] ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q := Ideal.Quotient.mkₐ F q
  let φ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k) →ₐ[F] ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q := π.comp (segreMap F)
  let R' : Subalgebra F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) := φ.range
  choose i hi using hq.relevant
  let x : K → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q := fun k => π (X ⟨k, i k⟩)
  have hx0 : ∀ k, x k ≠ 0 := fun k h =>
    hi k (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [x, π, Ideal.Quotient.mkₐ_eq_mk] using h))

  have hkey : ∀ k (j : ι k), (∏ l ∈ Finset.univ.erase k, x l) * π (X ⟨k, j⟩) =
      φ (X ⟨(), Function.update i k j⟩) := by
    intro k j
    rw [AlgHom.comp_apply, segreMap_X, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let k0 : K := Classical.arbitrary K
  let s : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) := x '' ↑(Finset.univ.erase k0)
  let B : Subalgebra R' (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) := Algebra.adjoin R' s
  have hR'B : ∀ a ∈ R', IsAlgebraic B a := fun a ha =>
    isAlgebraic_algebraMap (⟨a, Subalgebra.algebraMap_mem B (⟨a, ha⟩ : R')⟩ : B)
  have hsB : ∀ l, l ≠ k0 → IsAlgebraic B (x l) := fun l hl =>
    isAlgebraic_algebraMap (⟨x l, Algebra.subset_adjoin
      ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), rfl⟩⟩ : B)
  have hgen : ∀ k, (∀ l, l ≠ k → IsAlgebraic B (x l)) → ∀ j : ι k, IsAlgebraic B (π (X ⟨k, j⟩)) := by
    intro k hk j
    have hy : IsAlgebraic B (∏ l ∈ Finset.univ.erase k, x l) :=
      Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isAlgebraic_one
        fun l hl => hk l (Finset.ne_of_mem_erase hl)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ?_) hy ?_
    · exact Finset.prod_ne_zero_iff.mpr fun l _ => hx0 l
    · rw [hkey]
      exact hR'B _ ⟨_, rfl⟩
  have hall : ∀ l, IsAlgebraic B (x l) := by
    intro l
    by_cases hl : l = k0
    · subst hl
      exact hgen _ hsB (i _)
    · exact hsB l hl
  have hA : ∀ a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q, IsAlgebraic B a := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective F q a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.algHom_C]
      exact hR'B _ (R'.algebraMap_mem c)
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hgen v.1 (fun l _ => hall l) v.2)
  have : Algebra.IsAlgebraic B (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) := ⟨hA⟩
  have htop : Algebra.trdeg R' (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) ≤ #s := Algebra.IsAlgebraic.trdeg_le_cardinalMk R' s
  have hs : #s ≤ (Fintype.card K - 1 : ℕ) := by
    refine Cardinal.mk_image_le.trans ?_
    simp
  have : FaithfulSMul F R' :=
    (faithfulSMul_iff_algebraMap_injective F R').mpr (algebraMap F R').injective
  have : FaithfulSMul R' (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) :=
    ⟨fun {r₁ r₂} h => Subtype.ext (by simpa [Subalgebra.smul_def] using h 1)⟩
  have htower := trdeg_add_eq (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) F R'

  let g : (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k) ⧸ segrePrime F q) →ₐ[F] R' :=
    Ideal.Quotient.liftₐ (segrePrime F q) φ.rangeRestrict fun p hp => by
      apply Subtype.ext
      simpa [φ, π, segrePrime, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hp
  have hg : Function.Surjective g := by
    rintro ⟨y, p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hR'le := trdeg_le_of_surjective g hg
  obtain ⟨n, hn, htn⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q)
  obtain ⟨m, hm, htm⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k) ⧸ segrePrime F q)
  have hne : n = e + Fintype.card K := by
    rw [hn] at hdim
    exact_mod_cast hdim
  have hcard : (n : Cardinal) ≤ (m + (Fintype.card K - 1) : ℕ) := by
    rw [← htn, ← htower, Nat.cast_add, ← htm]
    exact add_le_add hR'le (htop.trans hs)
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hnm : n ≤ m + (Fintype.card K - 1) := by exact_mod_cast hcard
  rw [hm]
  exact_mod_cast (show e + 1 ≤ m by omega)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
