module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSourceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapFactorIsLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapUnipotentLawStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapTranslationLawsJacobiToBesselFreeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFourierJacobiToBesselColumnMulLaws

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatColLawFB

open GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frame_col (p : Place D k) {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (hB : p.IsBesFrame B (s * p.xi) FA FV)
    (j : Fin (σ + 1)) (l : Fin c) (hl : l.val = j.val) (x : Fin B.V.rank) :
    FV.β x (Sum.inr l) = s * p.xi ^ (σ + 1 - j.val) * ((xLast B.d (vecB B.o B.ζ)).map p.π) x j := by
  obtain ⟨-, -, hX, hz, -⟩ := hB
  induction j using Fin.lastCases with
  | last =>
    rw [hz l hl x]
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last, Fin.val_last, Nat.add_sub_cancel_left, pow_one]
    congr 1

    simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  | cast j =>
    rw [hX j l hl x]
    have hj := j.isLt
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc, Fin.val_castSucc]
    rw [show σ + 1 - j.val = (σ - j.val) + 1 by omega, pow_succ', ← mul_assoc]
    rfl

theorem flatFB_mulcol : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ σ ∧ ¬ Free (σ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hjac _ hbes Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * σ + 1 := hbes.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin (σ + 1) := ⟨i.val, by omega⟩
  let zk : Matrix (Fin (σ + 1)) (Fin B.V.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (σ + 1 - i.val)) * FV.γ r β else 0
  let a : Mx D B.V.rank (σ + 1) := giA B.V * adj (zk.map p.ι : Mx D (σ + 1) B.V.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (J.d.extY B.V a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin (σ + 1), (FV.γ * (xLast B.d (vecB B.o B.ζ)).map p.π) r j = (s * p.xi ^ (σ + 1 - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FV.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (frame_col p B s FA FV hbes j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO J.W B.V (p.up FW FV t) (J.d.extY B.V a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FV.γβ, Matrix.one_mul,
      col_mul _ _ FW.β i₀ (Sum.inr i) (hκ _) (hjac.2.2.1 i₀ i rfl), Matrix.mul_assoc, FW.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO J.W B.V (J.d.extX B.V (xLast B.d (vecB B.o B.ζ))) (J.d.extY B.V a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv B.V (xLast B.d (vecB B.o B.ζ)) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).2 σ J B st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatFB_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLawFB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFourierJacobiToBesselColumnMulLawsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flat_fourierJacobi_to_bessel_column_mul_laws : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ σ ∧ ¬ Free (σ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.FlatColLawFB.flatFB_mulcol | exact GlobalTheory.FlatColLawFB.flatFB_mulcol | (intros; apply GlobalTheory.FlatColLawFB.flatFB_mulcol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapRowMultiplication

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section
open GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.MulRow

variable {D : D7}

theorem infPart_half {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : cA D e * z = z) : infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem pr_ne {a : D.host.E} (ha : a ≠ 0) : p.pr a ≠ 0 := by
  intro h
  have h1 : p.pr a * p.pr a⁻¹ = 1 := by
    unfold Place.pr
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem pr_dot {N M : ℕ} (Q : Matrix (Fin M) (Fin N) D.host.E) (v : Fin N → D.host.E) (i : Fin M) (a : k) :
    ∑ r, p.pr (Q i r) * (a * p.pr (v r)) = a * p.pr ((Q *ᵥ v) i) := by
  unfold Place.pr

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem pr_zero : p.pr 0 = 0 := by unfold Place.pr; rw [map_zero, map_zero]

theorem pr_one : p.pr 1 = 1 := by unfold Place.pr; rw [map_one, map_one]

theorem pr_map_mul {L M N : ℕ} (X : Matrix (Fin L) (Fin M) D.host.E) (Y : Matrix (Fin M) (Fin N) D.host.E) :
    (X * Y).map p.pr = X.map p.pr * Y.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem hO_iso {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (x : WO S T) (N : Mx D S₀.rank σ) :
    hO S T x (dS.ext0 T (dT.incX S₀ (adj (gA S₀ ⬝ N)))) = (N ⬝ (dT.pY ⬝ (x ⬝ dS.j0))).trace := by
  rw [dS.hO_coordS]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_j0, HypDec.p0_jY,
    Matrix.mul_one, Matrix.mul_zero, pairS, adj_zero, Matrix.zero_mul, trace_zero, zero_add, add_zero, hO_eq_trace]
  rw [adj_mul dT.jX, adj_adj, HypDec.pY_eq]
  simp only [Matrix.mul_assoc, giA_gA_cancel]

theorem qY_frame {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (hB : p.IsBesFrame B s FA FV)
    (i : Fin σ) (l : Fin c) (hl : l.val + i.val = 2 * σ) (r : n ⊕ Fin c) :
    (B.d.qY.map p.pr * FV.β) i r =
      if r = Sum.inr l then s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - i.val) else 0 := by
  obtain ⟨hc, h0, hX, hz, hY⟩ := hB
  have q0 : B.d.qY * B.d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pY_j0)
  have qX : B.d.qY * B.d.e = 0 := B.d.ee
  have qY : B.d.qY * B.d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact B.d.pY_jY)
  rcases r with a | j
  · rw [if_neg Sum.inl_ne_inr, Matrix.mul_apply]
    simp only [h0]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← pr_map_mul, ← Matrix.mul_assoc, q0, Matrix.zero_mul,
      Matrix.map_zero _ (pr_zero p), Matrix.zero_mul, Matrix.zero_apply]
  · have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    rcases lt_trichotomy j.val σ with h | h | h
    · simp only [hX ⟨j.val, h⟩ j rfl]
      rw [pr_dot p B.d.qY (fun r => B.d.e r ⟨j.val, h⟩),
        show (B.d.qY *ᵥ fun r => B.d.e r ⟨j.val, h⟩) i = (B.d.qY * B.d.e) i ⟨j.val, h⟩ from rfl, qX,
        Matrix.zero_apply, pr_zero, mul_zero, if_neg]
      intro e; cases e; omega
    · simp only [hz j h]
      rw [pr_dot p B.d.qY, Matrix.mulVec_mulVec, q0, Matrix.zero_mulVec, Pi.zero_apply, pr_zero, mul_zero, if_neg]
      intro e; cases e; omega
    · have hi' : 2 * σ - j.val < σ := by omega
      simp only [hY ⟨2 * σ - j.val, hi'⟩ j (by simp only; omega)]
      rw [pr_dot p B.d.qY (fun r => B.d.e' r ⟨_, hi'⟩),
        show (B.d.qY *ᵥ fun r => B.d.e' r ⟨_, hi'⟩) i = (B.d.qY * B.d.e') i ⟨_, hi'⟩ from rfl, qY]
      by_cases e : j = l
      · subst e
        have : i = ⟨_, hi'⟩ := Fin.ext (by simp only; omega)
        rw [← this, Matrix.one_apply_eq, pr_one, mul_one, if_pos rfl]
        congr 2
        omega
      · rw [Matrix.one_apply_ne, pr_zero, mul_zero, if_neg (fun h => e (Sum.inr_injective h))]
        intro h'
        apply e
        have := congrArg Fin.val h'
        exact Fin.ext (by simp only at this; omega)

theorem exists_row (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : k) (hs : s ≠ 0)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (hh : k)
    (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n)
    (FV : Frame k B.V.rank (n ⊕ Fin c)) (hJ : p.IsJacFrame J s hh G₀ FW) (hB : p.IsBesFrame B (s * p.xi) FA FV)
    (l : Fin c) (s' : n') (hl : σ < l.val) (b : k) : ∃ ξ : Mx D σ J.W₀.rank, (∀ i j, cA D p.e * ξ i j = ξ i j) ∧
      ∀ t, p.π (hO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.incX J.W₀ ξ))) = b * t (Sum.inr l) (Sum.inl s') := by
  have hc := hB.1
  have hl' := l.isLt
  have hi : 2 * σ - l.val < σ := by omega
  have hxi : p.xi ≠ 0 := pr_ne p (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hz : p.hz B ≠ 0 := pr_ne p B.line.2
  obtain ⟨i, hli⟩ : ∃ i : Fin σ, l.val + i.val = 2 * σ := ⟨⟨_, hi⟩, by simp only; omega⟩
  have hrow := qY_frame p B _ FA FV hB i l hli
  set u : k := s * p.xi * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - i.val) with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hs hxi) (div_ne_zero (neg_ne_zero.2 hz) hxi))
    (pow_ne_zero _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hxi))
  have hcol : ∀ q, (FW.γ * (J.d.i₀.map p.pr * G₀.β)) q s' = if q = Sum.inl s' then 1 else 0 := fun q => by
    rw [Matrix.mul_apply]
    simp only [← hJ.2.1]
    rw [← Matrix.mul_apply, FW.γβ, Matrix.one_apply]
  have hι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hπι : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) k), (M.map p.ι).map p.π = M := fun M => by
    ext i j; exact p.π_ι _
  refine ⟨adj (gA J.W₀ ⬝ ((G₀.β * Matrix.single s' i (b / u)).map p.ι : Mx D J.W₀.rank σ)), fun i j => ?_, fun t => ?_⟩
  · simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
    rw [← map_mul, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_left_comm, Matrix.map_apply, hι]
  · rw [hO_iso, AddMonoidHom.map_trace, Matrix.map_mul, hπι, Matrix.map_mul, Matrix.map_mul, Place.up, hπι]
    change ((G₀.β * Matrix.single s' i (b / u)) * (B.d.qY.map p.pr * (FV.β * t * FW.γ * J.d.i₀.map p.pr))).trace = _
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul]
    have e : B.d.qY.map p.pr * (FV.β * t * FW.γ * J.d.i₀.map p.pr) * G₀.β =
        (B.d.qY.map p.pr * FV.β) * (t * (FW.γ * (J.d.i₀.map p.pr * G₀.β))) := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_apply]
    simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Matrix.mul_apply]
    simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul]
    field_simp

end GlobalTheory.LocMod.MulRow


open GlobalTheory.LocMod.MulRow in
theorem GlobalTheory.LocMod.flatFB_mulrow : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s', r = Sum.inr l ∧ σ < l.val ∧ q = Sum.inl s') → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hch σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ _ hB Tm hM r q hrq b Φ Φ' hΦ
  obtain ⟨l, s', rfl, hl, rfl⟩ := hrq
  obtain ⟨ξ, hξh, hξ⟩ := exists_row p σ J B s hs n n' c _ G₀ FW FA FV hJ hB l s' hl b
  have hy : IsHalf (cA D p.e) (J.d.ext0 B.V (B.d.incX J.W₀ ξ)) := by
    have hξ' : cA D p.e • ξ = ξ := by ext i j; exact hξh i j
    have hm : cA D p.e • ((B.d.jX ⬝ ξ) ⬝ J.d.p0) = (B.d.jX ⬝ ξ) ⬝ J.d.p0 := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hξ']
    intro i j
    exact congrArg (fun M => M i j) hm
  have hsym : ∀ t, ψ (symplO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.incX J.W₀ ξ))) =
      (ψk (b * t (Sum.inr l) (Sum.inl s')) : ℂ) := by
    intro t
    rw [((GlobalTheory.T.heisenberg_frame_half_inverse D k p _ _ J.W B.V FW FV ψ ψk hch).2.2.2.1 t _ hy), hξ t]
  have h1 : Tm Φ' = heisO ψ J.W B.V (J.d.ext0 B.V (B.d.incX J.W₀ ξ)) (Tm Φ) := by
    refine hM.modul _ hy Φ Φ' fun t => ?_
    rw [hΦ t, hsym t]
    congr 4
    simp [basePt]
  have hmx : MxAt (fun _ => True) ξ := by
    intro i j
    refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_half p.split (hξh i j)), Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have hF := ((hFL ψ (fun _ => True)).2 σ J B st).Heisenberg₂
  have h0 : symplO J.W₀ B.V 0 (B.d.incX J.W₀ ξ) = 0 := by simp [symplO, hO]
  rw [h1, hF.iso (Tm Φ) (hM.theta Φ) ξ hmx, map_zero, h0, AddChar.map_zero_eq_one, one_smul]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapRowMultiplicationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.fourierJacobi_bessel_flatMap_row_multiplication : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s', r = Sum.inr l ∧ σ < l.val ∧ q = Sum.inl s') → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  first | exact @GlobalTheory.LocMod.flatFB_mulrow | exact GlobalTheory.LocMod.flatFB_mulrow | (intros; apply GlobalTheory.LocMod.flatFB_mulrow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem _root_.GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (f g : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → IsThetaFunO ψ J.W B.V g → flatFB st (f + g) = flatFB st f + flatFB st g ∧ ∀ a : ℂ, flatFB st (a • f) = a • flatFB st f := by
  first | exact @GlobalTheory.FlatAdd.flatFB_add_smul | exact GlobalTheory.FlatAdd.flatFB_add_smul | (intros; apply GlobalTheory.FlatAdd.flatFB_add_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocMod

theorem flatFB_holds : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd).2.1 ψk hχ
  have hc : c = 2 * σ + 1 := hBF.1
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ) :=
    { toFun := fun Φ => flatFB st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add (f := _)]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ)).2 a }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source k ψk ν hcont hne hν n n' c σ (WO J.W₀ B.V₀ → ℂ) L hc
    (GlobalTheory.T.flat_fourierJacobi_to_bessel_column_mul_laws D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_row_multiplication D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.localFlatMap_translationLaws_jacobiToBessel_free D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_unipotent_law D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
  exact ⟨L₀, GlobalTheory.T.fourierJacobi_bessel_flatMap_factor_isLocalModel D hFLs hOm k p ν hν ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm L₀ hL₀, hL₀⟩

end GlobalTheory.LocMod

end
end
end
