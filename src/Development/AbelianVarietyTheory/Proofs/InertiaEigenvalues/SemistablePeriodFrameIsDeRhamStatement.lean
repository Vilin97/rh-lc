module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodCocycleFrobeniusRelationOnDiscStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDisc

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.FrobTwistKappa

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  intro l _ K bk τ d ρ s g G Φ i Ψ V ε hG hΦ hi hΨ hκ h
  have hsmul : ∀ (f : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map f = f c • M.map f := fun f c M => by ext a b; simp
  have hΦG : ∀ x, Φ (G x) = G (Φ x) := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun a => (GlobalTheory.Prism.PullGal.σA_frobenius (g : GQ l) a).symm
    have hc := (GlobalTheory.BSP.FrobRational.isDiscMap_comp hG hΦ).unique
      (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΦ hG)
    exact fun x => RingHom.congr_fun hc x
  have hΦi : Φ.comp i = i.comp Ψ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev = bk.ev.comp (frobS l bk.a) :=
      RingHom.ext fun x => (bk.ev_frob x).symm
    exact (GlobalTheory.BSP.FrobRational.isDiscMap_comp hi hΦ).unique (e ▸ GlobalTheory.BSP.FrobRational.isDiscMap_comp hΨ hi)
  have hΦiS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (toDisc l (bk.ev X) bk.ρ₀ (bk.ev x)) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have hFD : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C)).map i = s.F.map (bk.iS.comp C) := by
    ext a b
    exact hi.ext _
  have hGFD : (s.F.map (bk.iS.comp C)).map G = s.F.map (bk.iS.comp C) := by
    ext a b
    change G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))) = toDisc l (bk.ev X) bk.ρ₀ (bk.ev (C (s.F a b)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have e1 : (V.map i).map Φ = (V.map Ψ).map i := by
    ext a b
    exact RingHom.congr_fun hΦi (V a b)
  have e2 : (ε.map bk.iA).map Φ = (ε.map WittVector.frobenius).map bk.iA := by
    ext a b
    exact hΦ.ext _
  have e3 : ((V.map i).map G).map Φ = ((V.map Ψ).map i).map G := by
    ext a b
    simp only [Matrix.map_apply]
    rw [hΦG]
    exact congrArg G (RingHom.congr_fun hΦi (V a b))
  have h1 := congrArg (fun M => M.map Φ) h
  simp only [hsmul, Matrix.map_mul] at h1
  rw [map_pow, map_pow, hΦG, hΦiS, e1, e2, e3] at h1
  have eL : (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i =
      s.F.map (bk.iS.comp C) * (V.map Ψ).map i := by
    rw [Matrix.map_mul, hFD]
  rw [eL, Matrix.map_mul, hGFD, Matrix.mul_assoc (s.F.map (bk.iS.comp C)), ← Matrix.mul_assoc (s.κ g), hκ,
    Matrix.mul_assoc]
  have h2 := congrArg (fun M => s.F.map (bk.iS.comp C) * M) h1
  simp only [Matrix.mul_smul] at h2
  exact h2

end GlobalTheory.BKLim.FrobTwistKappa
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDiscStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  first | (exact @GlobalTheory.BKLim.FrobTwistKappa.main) | (exact GlobalTheory.BKLim.FrobTwistKappa.main) | (intros; apply GlobalTheory.BKLim.FrobTwistKappa.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameFrobeniusIsUnitDisc

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem isUnit_map_of_mul_eq_smul {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (g : R →+* D)
    (M M' : Matrix (Fin d) (Fin d) R) (r : R) (h : M * M' = r • (1 : Matrix (Fin d) (Fin d) R)) (hr : IsUnit (g r)) :
    IsUnit (M.map g) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 : M.map g * M'.map g = g r • (1 : Matrix (Fin d) (Fin d) D) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hr.pow d)

theorem wseed_F_frob_XZ_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  intro l _ K bk τ d ρ s Ψ Z hΨ hZ
  have hl := isUnit_l_disc l (X : bk.S) bk.ρ₀
  rw [Matrix.map_mul]
  refine IsUnit.mul ?_ (IsUnit.mul ?_ ?_)
  · refine isUnit_map_of_mul_eq_smul _ s.F s.F' _ s.F_mul ?_
    rw [map_pow, map_natCast]
    exact hl.pow _
  · have e : Ψ.comp (toDisc l (X : bk.S) bk.ρ₀) = (toDisc l (X : bk.S) bk.ρ₀).comp (frobS l bk.a) :=
      RingHom.ext hΨ.ext
    rw [Matrix.map_map, show (⇑Ψ ∘ ⇑(toDisc l (X : bk.S) bk.ρ₀)) = ⇑(Ψ.comp (toDisc l (X : bk.S) bk.ρ₀)) from rfl, e]
    refine isUnit_map_of_mul_eq_smul _ s.X s.X' _ s.X_mul ?_
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
    exact (hl.pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  · exact hZ.map (Ψ.mapMatrix)

end GlobalTheory.BKLim

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameFrobeniusIsUnitDiscStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  first | (exact @GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (exact GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (intros; apply GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRham

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.WDR

theorem frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  intro l hl K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ hκ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨hmap, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i, hi⟩ := hmap _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Ψ, hΨ⟩ := hmap _ _ (frobS l bk.a) (X : bk.S) (X : bk.S) bk.ρ₀ bk.ρ₀ l h0 (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := hmap _ _ (WittVector.frobenius : Ainf l →+* Ainf l) (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ l h0
    (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  set V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z with hV
  have hVi : V.map i = s.X.map bk.iS * Z.map i := by
    rw [hV, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  set H := s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ with hH
  have hHu : IsUnit H := GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc l K bk τ d ρ s Ψ Z hΨ hZ
  intro m
  exact GlobalTheory.T.exists_beta_of_disc_cocycle_alt l K bk d s.N s.κ (fun g => (F.ε g).map WittVector.frobenius) H i hi hHu s.log
    (fun g G hG => GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc l K bk τ d ρ s g G Φ i Ψ V (F.ε g) hG hΦ hi hΨ
      (GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc l K bk τ hτ d ρ hρ s g G Φ hG hΦ) (by rw [hVi]; exact hκ g G i hG hi)) m

end GlobalTheory.BKLim.WDR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRhamStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriodFrame_isDeRham : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → F.IsDR := by
  first | (exact @GlobalTheory.BKLim.WDR.frame_isDR) | (exact GlobalTheory.BKLim.WDR.frame_isDR) | (intros; apply GlobalTheory.BKLim.WDR.frame_isDR  <;> assumption)
end
end
