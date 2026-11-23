module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompData
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjCmHostRootNeSelf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeafCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h5
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h5
  have h6 := H.sqrt_neg_disc_sq
  rw [hx] at h6
  have h7 : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast h6
  have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg x]

theorem tauEmb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauEmb_ne_conj (Q : Par D) (hp : Q.PinHost) (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 := hp.2.2.2 t
  rw [h] at h1
  have h2 : (starRingEnd ℂ) (DV.tauEmb D t' (Q.H.rt : D.host.E)) = Q.H.rt0 := h1
  rw [hp.2.2.2 t'] at h2
  exact conj_cmHostRoot_ne_self Q.H h2

theorem exists_tau (Q : Par D) (hp : Q.PinHost) (τ : D.host.E →+* ℂ) (hτ : InPsi Q.H τ) :
    ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
  by_cases hgP : g ∈ D.R.Psi
  · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
    exact ⟨t, hg.symm.trans ht⟩
  · exfalso
    have h2 : g * D.R.cc ∈ D.R.Psi := by
      by_contra h
      exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
    obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
    have h3 : DV.tauEmb D t (Q.H.rt : D.host.E) = Q.H.rt0 := hp.2.2.2 t
    rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
    have h4 : τ (D.host.conj (Q.H.rt : D.host.E)) = star (τ (Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
    have hτ' : τ (Q.H.rt : D.host.E) = Q.H.rt0 := hτ
    apply conj_cmHostRoot_ne_self Q.H
    calc star Q.H.rt0 = star (τ (Q.H.rt : D.host.E)) := by rw [hτ']
      _ = τ (D.host.conj (Q.H.rt : D.host.E)) := h4.symm
      _ = Q.H.rt0 := h3

theorem wtA_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [tauEmb_ne_conj Q hp]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (tauEmb_inj h).symm
    simp [tauEmb_ne_conj Q hp, this]
  · simp

end GlobalTheory.LeafCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FrameNormRestrictedDensity

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Core D}

abbrev FrameNorms (T : Core D) (j : ℕ) : Type :=
  ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ

abbrev GenericFrames (T : Core D) (j : ℕ) : Type :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))

end GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.NotRestrDensityRescale

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LowerBoundCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.IndefiniteRowSideFullHecke.FrameNormRestrictedDensity

variable {D : D7} {T : Core D}

theorem conjEmb_invol {E : Type} [Field E] (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem wtA_conj_tau (Q : Par D) (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  have h1 : ∀ t', conjEmb (DV.tauEmb D t) ≠ DV.tauEmb D t' := fun t' h =>
    GlobalTheory.LeafCompare.tauEmb_ne_conj Q hp t' t h.symm
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [h1]
  · intro t' _ ht'
    have : conjEmb (DV.tauEmb D t) ≠ conjEmb (DV.tauEmb D t') := fun h =>
      ht' (GlobalTheory.LeafCompare.tauEmb_inj (by
        rw [← conjEmb_invol (DV.tauEmb D t'), ← h, conjEmb_invol]))
    simp [h1, this]
  · simp

theorem wt_ext (Q : Par D) (hp : Q.PinHost) {j : ℕ} {w w' : WeightFamilies.Wt D j} (hA : wtA w = wtA w') (hn : w.n = w'.n) :
    w = w' := by
  have hP : w.aP = w'.aP := by
    funext t i
    have := congrFun hA (DV.tauEmb D t, i.1)
    rw [GlobalTheory.LeafCompare.wtA_tau Q hp, GlobalTheory.LeafCompare.wtA_tau Q hp] at this
    simpa [ext0, i.2] using this
  have hM : w.aM = w'.aM := by
    funext t i
    have := congrFun hA (conjEmb (DV.tauEmb D t), i.1)
    rw [wtA_conj_tau Q hp, wtA_conj_tau Q hp] at this
    simpa [ext0, i.2] using this
  cases w
  cases w'
  simp only at hP hM hn
  subst hP hM hn
  rfl

theorem wtA_wsmul_apply {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) (x : (D.host.E →+* ℂ) × ℕ) :
    wtA (WeightAlgebra.wsmul k w) x = k * wtA w x := by
  have h0 : ∀ {p : ℕ} (f : Fin p → ℕ) (i : ℕ), ext0 (fun s => k * f s) i = k * ext0 f i := by
    intro p f i
    unfold ext0
    split_ifs <;> simp
  simp only [wtA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ext0 ((WeightAlgebra.wsmul k w).aP t) x.2 = k * ext0 (w.aP t) x.2 := h0 _ _
  have h2 : ext0 ((WeightAlgebra.wsmul k w).aM t) x.2 = k * ext0 (w.aM t) x.2 := h0 _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

theorem eq_wsmul_iff (h : LawsCore T) {j : ℕ} (ka wL : WeightFamilies.Wt D j) (n : ℕ) :
    wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n ↔ ka = WeightAlgebra.wsmul n wL := by
  constructor
  · intro H
    refine wt_ext T.Q h.pins.1 (funext fun x => ?_) ?_
    · have : (wtA ka x : ℤ) = n • (wtA wL x : ℤ) := congrFun (congrArg Prod.fst H) x
      rw [nsmul_eq_mul] at this
      rw [wtA_wsmul_apply]
      exact_mod_cast this
    · have : (ka.n : ℤ) = n • (wL.n : ℤ) := congrArg Prod.snd H
      rw [nsmul_eq_mul] at this
      show ka.n = n * wL.n
      exact_mod_cast this
  · rintro rfl
    refine Prod.ext (funext fun x => ?_) ?_
    · simp only [wtZ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, wtA_wsmul_apply]
      push_cast
      rfl
    · simp only [wtZ, Prod.smul_snd, nsmul_eq_mul]
      show ((n * wL.n : ℕ) : ℤ) = _
      push_cast
      rfl

section Density

variable (h : LawsCore T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (fn : FrameNorms T j) (yP : GenericFrames T j)
  (ka : WeightFamilies.Wt D j)

end Density

section Separate

variable {j : ℕ}

end Separate

end GlobalTheory.LowerBoundCompare
end
end
end
