module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Mathlib.Tactic.Have
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceUpWittExtendByZeroRankZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.RankZeroSrc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_incA (p : Place D k) (x : k) (a : D.host.E) : p.ι x * (incA D a : AE D) = p.ι (x * p.pr a) := by
  have h : x * p.pr a = p.π (p.ι x * (incA D a : AE D)) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, ← mul_assoc, Witness.e_ι]

theorem map_ι_mul_rat (p : Place D k) {l m : ℕ} {Y : Type} [Fintype Y] (N : Matrix Y (Fin l) k)
    (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι) * (rat M : Matrix (Fin l) (Fin m) (AE D)) = (N * M.map p.pr).map p.ι := by
  ext i j

  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_incA]

theorem fromCols_toCols₁ {Z n : Type} (x : Matrix Z (n ⊕ Fin 0) k) : fromCols x.toCols₁ 0 = x := by
  conv_rhs => rw [← Matrix.fromCols_toCols x]
  congr 1
  ext i j
  exact j.elim0

theorem splitLocalPlace_up_wittExtendByZero_rankZero (p : Place D k) {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (J : JacLev D 0)
    (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin 0)) (hF : p.IsJacFrame J s hh F₀ F) (T : HSp D)
    (FT : Frame k T.rank Z) (x : Matrix Z n k) :
    J.d.ext0 T (p.up F₀ FT x) = p.up F FT (fromCols x 0) := by
  have hq : J.d.q0 * J.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact J.d.p0_j0)
  have hq' : J.d.q0.map p.pr * J.d.i₀.map p.pr = 1 := by
    rw [← show (J.d.q0 * J.d.i₀).map p.pr = J.d.q0.map p.pr * J.d.i₀.map p.pr from Matrix.map_mul (f := Witness.prH p), hq]
    exact Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))
  have hβ : F.β.toCols₁ = J.d.i₀.map p.pr * F₀.β := by ext r a; exact hF.2.1 r a
  have h1 : F.β * F.γ = 1 := F.βγ
  have h0 : F.β.toCols₂ * F.γ.toRows₂ = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [← Matrix.fromCols_toCols F.β, ← Matrix.fromRows_toRows F.γ, Matrix.fromCols_mul_fromRows, h0, add_zero, hβ] at h1
  have hγ : F.γ.toRows₁ = F₀.γ * J.d.q0.map p.pr := by
    have e : F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F.γ.toRows₁ := by
      rw [show F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) =
          F₀.γ * (J.d.q0.map p.pr * J.d.i₀.map p.pr) * F₀.β * F.γ.toRows₁ by simp only [Matrix.mul_assoc],
        hq', Matrix.mul_one, F₀.γβ, Matrix.one_mul]
    rw [← e, h1, Matrix.mul_one]
  rw [HypDec.matrixExtendByZero_apply]
  unfold Place.up
  rw [HypDec.p0, map_ι_mul_rat]
  congr 1
  conv_rhs => rw [← Matrix.fromRows_toRows F.γ, Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero, hγ]
  simp only [Matrix.mul_assoc]

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w w' : WO S₀ T) :
    symplO S T (d.ext0 T w) (d.ext0 T w') = symplO S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  unfold symplO
  rw [h]

theorem wittExtensionByZero_preserves_isHalf {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {e : AE D} {y : WO S₀ T} (hy : IsHalf e y) :
    IsHalf e (d.ext0 T y) := fun i j => by
  rw [HypDec.matrixExtendByZero_apply, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy i l]

end GlobalTheory.LocMod.RankZeroSrc

namespace GlobalTheory.LocMod.RankZeroSrc

theorem localModel_rankZeroWitt_source_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (J : JacLev D 0) (s hh : k) (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) (F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin 0)), p.IsJacFrame J s hh F₀ F → ∀ (T : HSp D) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (Tm : SB (Matrix Z (n ⊕ Fin 0) k) →ₗ[ℂ] (WO J.W T → ℂ)), p.IsModel ψ F FT Tm → ∃ T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ), p.IsModel ψ F₀ FT T₂ ∧ ∀ (Ψ : SB (Matrix Z n k)) (Φ : SB (Matrix Z (n ⊕ Fin 0) k)), (∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) → ∀ w, T₂ Ψ w = Tm Φ (J.d.ext0 T w) := by
  intro D k _ _ _ _ p ψ hψ J s hh n Z _ _ _ _ F₀ F hF T FT Tm hM
  have hT := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ J.W J.W₀ T J.d hψ
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z) (n' := n ⊕ Fin 0)
  have hc1 : Continuous fun x : Matrix Z (n ⊕ Fin 0) k => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => by
      show Continuous fun a : Matrix Z (n ⊕ Fin 0) k => a i (Sum.inl j)
      exact (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · show Continuous fun a : Matrix Z n k => a i j
        exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  let R : SB (Matrix Z n k) → SB (Matrix Z (n ⊕ Fin 0) k) := fun Ψ =>
    ⟨fun x => Ψ.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 fromCols_toCols₁⟩
  have hR : ∀ Ψ x, (R Ψ).1 x = Ψ.1 x.toCols₁ := fun _ _ => rfl
  let T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ) :=
    { toFun := fun Ψ w => Tm (R Ψ) (J.d.ext0 T w)
      map_add' := fun Ψ Ψ' => by
        funext w
        rw [show R (Ψ + Ψ') = R Ψ + R Ψ' from Subtype.ext rfl, map_add (f := _)]
        rfl
      map_smul' := fun c Ψ => by
        funext w
        rw [show R (c • Ψ) = c • R Ψ from Subtype.ext rfl, map_smul]
        rfl }
  have hT₂ : ∀ Ψ w, T₂ Ψ w = Tm (R Ψ) (J.d.ext0 T w) := fun _ _ => rfl
  have hup : ∀ x, p.up F FT x = J.d.ext0 T (p.up F₀ FT x.toCols₁) := fun x => by
    rw [splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT, fromCols_toCols₁]
  refine ⟨T₂, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun Ψ Φ h w => ?_⟩
  · exact (hT.2.2.1 (Tm (R Ψ))).2 (hM.theta _)
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (p.up F FT (fromCols x 0)) (Tm (R Ψ)) := hM.trans _ _ _ fun t => by
      rw [hR, hR, h]
      congr 1
    funext w
    rw [hT₂, e1, ← splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (J.d.ext0 T y) (Tm (R Ψ)) := hM.modul _ (wittExtensionByZero_preserves_isHalf J.d T hy) _ _ fun t => by
      rw [hR, hR, h, hup, wittExtensionByZero_symplectic_form_eq]
    funext w
    rw [hT₂, e1]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · rw [hT₂, show R Ψ = Φ from Subtype.ext (funext fun x => by rw [hR, h, fromCols_toCols₁])]

end GlobalTheory.LocMod.RankZeroSrc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStep

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.LastStepExt0

theorem model_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj h₃ h₄
  suffices key : ∀ (n : ℕ) (hn : j + 1 + 1 = n) (hnm : n ≤ D.R.m)
      (h₃' : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, n)),
      ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m n)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w n hnm) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G hn (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃') (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G hn (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)
  · exact key D.R.m (by omega) le_rfl h₃
  intro n hn hnm h₃'
  subst hn
  have hj1 : j + 1 < D.R.m := by omega
  have hc : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have hloc : ∀ i (hi : i ≤ D.R.m), D.R.m ≤ i + 1 →
      p.IsLoc (frRow ch.S.B t w i hi) 1 ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, i)) := by
    intro i hi hmi
    rw [Pi.mul_apply, epsV_eq_one t w hmi, elt_eq_one t w β hmi, mul_one]
    refine ⟨fun a b => by simp [Formalism.L2.Theta.mt], ?_⟩
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m i)) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp [(frRow ch.S.B t w i hi).βγ]
  obtain ⟨Tm, hTm, hOne, Φ, hΦ, hTΦ⟩ := hArr t w hw p hp φ (j + 1) hj1 (v ⟨j + 1, hj1⟩) (f ⟨j + 1, hj1⟩) (hvf ⟨j + 1, hj1⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem t w X) 1 1 1 1 (hloc (j + 1) hj1.le (by omega))
    (hloc (j + 1 + 1) hj1 (by omega)) (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
    (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (frame hc) (Equiv.refl _)
  have hJ := hJac t w hw p hp M hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt ch.G j 0 hj)).some 1 (Or.inl ⟨rfl, rfl⟩) 0 hc
  have hFT : (mvFr p (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1)))) (frRow ch.S.B t w (j + 1 + 1) hj1)
      (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)).β = (frRow ch.S.B t w (j + 1 + 1) hj1).β := by
    simp only [mvFr]
    rw [epsV_eq_one t w (by omega)]
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1 + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp
  obtain ⟨Tm', hTm', hTT⟩ := Place.exists_isModel_chg D (Kw w) p _ _ _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (mvFr p 1 (frRow ch.S.B t w (j + 1 + 1) hj1) (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)) _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (frRow ch.S.B t w (j + 1 + 1) hj1) ch.W.ψ Tm hTm
  have hTT' : ∀ Ψ, Tm' Ψ = Tm Ψ := fun Ψ => hTT Ψ Ψ fun x => by
    rw [hFT, Frame.γβ, Frame.γβ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨T₂, hT₂, hval⟩ := RankZeroSrc.localModel_rankZeroWitt_source_isModel D (Kw w) p ch.W.ψ ch.W.ψ_std (jacAt ch.G hM (j + 1) 0 (by omega)) _ _ _ _
    (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hJ _ (frRow ch.S.B t w (j + 1 + 1) hj1) Tm' hTm'
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)))
  have hc1 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w) => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w) =>
        (fromCols x 0 : Matrix _ (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  refine ⟨T₂, hT₂, fun O hO => ?_, ?_⟩
  · let O' : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
        (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
      ⟨fun x => O.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB O.2 hc1 hc2 RankZeroSrc.fromCols_toCols₁⟩
    have hO' : IsOne O' := by
      funext x
      show O.1 x.toCols₁ = _
      rw [hO]
      by_cases h2 : ∀ r q, x r q ∈ 𝒪[Kw w]
      · rw [Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) (a := x.toCols₁) (fun r q => h2 r (Sum.inl q)),
          Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2]
      · rw [Set.indicator_of_notMem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2, Set.indicator_of_notMem (a := x.toCols₁)]
        intro h1
        apply h2
        intro r q
        rcases q with q | q
        exacts [h1 r q, q.elim0]
    funext x
    refine (hval O O' (fun y => by simp [O', Matrix.toCols₁_fromCols]) x).trans ?_
    refine (congrFun (hTT' O') _).trans ?_
    refine (congrFun (hOne O' hO') _).trans ?_
    simp only [show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
      map_one, Module.End.one_apply]
    rfl
  · let Φ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
      ⟨fun x => Φ.1 (fromCols x 0), GlobalTheory.FinPl.Comm.comp_mem_SB Φ.2 hc2 hc1 fun x => Matrix.toCols₁_fromCols x 0⟩
    have hs : ∀ b, (frame hc).symm b = Sum.inl (Fin.cast h₄ b) := fun b => by
      rw [Equiv.symm_apply_eq]
      ext
      rfl
    refine ⟨Φ₂, fun z => ?_, ?_⟩
    · show Φ.1 (fromCols z 0) = _
      rw [hΦ]
      congr 2
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, hs, Matrix.fromCols_apply_inl]
      rfl
    · funext x
      refine (hval Φ₂ Φ (fun _ => rfl) x).trans ?_
      refine (congrFun (hTT' Φ) _).trans ?_
      refine (congrFun hTΦ _).trans ?_
      simp only [mul_one, show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
        map_one, Module.End.one_apply]
      rfl

end GlobalTheory.LastStepExt0
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStepStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  first | exact @GlobalTheory.LastStepExt0.model_last | exact GlobalTheory.LastStepExt0.model_last | (intros; apply GlobalTheory.LastStepExt0.model_last <;> assumption)
end
end
