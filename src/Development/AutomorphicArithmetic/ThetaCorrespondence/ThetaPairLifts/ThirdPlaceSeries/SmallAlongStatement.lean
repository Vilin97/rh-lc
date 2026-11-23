module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.ParConsts
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealTStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModelStatement
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem four_f_r_le_k_pow_eight (R : Ranks) : 4 * R.f * R.r ≤ R.k ^ 8 := by
  have hf : R.f ≤ R.k := by
    unfold Ranks.f Ranks.n
    exact R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hr : R.r ≤ 2 * R.k := by
    unfold Ranks.r
    omega
  have hk : 2 ≤ R.k := by omega
  have h6 : 8 ≤ R.k ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)
  calc 4 * R.f * R.r ≤ 4 * R.k * (2 * R.k) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = 8 * R.k ^ 2 := by ring
    _ ≤ R.k ^ 6 * R.k ^ 2 := Nat.mul_le_mul_right _ h6
    _ = R.k ^ 8 := by ring

theorem four_f_r_le_min_g_of_sizeG {D : D7} (L : SizeData₂ D) (h : SizeG L) : Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D := by
  have hb : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _)
  have key : ∀ i : Fin 2, 4 * D.R.f * D.R.r ≤ D.host.g i := by
    intro i
    have h1 := (h i i).1
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
      pow_le_pow_left₀ hk (le_mul_of_one_le_right hk hb) 8
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
    exact (four_f_r_le_k_pow_eight D.R).trans h3
  unfold Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound
  exact le_min (key 0) (key 1)

theorem four_f_r_le_min_g_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x →
    ∀ i : Fm.Ix x, Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound (Fm.D x i) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := Fm.sizes x hx i
  exact four_f_r_le_min_g_of_sizeG _ hG

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankComapOfLeRange

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.RowIso

theorem finrank_eq_of_semi {σ : ℂ →+* ℂ} (hσ : Function.Bijective σ) {E F : Type} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₛₗ[σ] F) (hf : Function.Bijective f) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective f.toAddMonoidHom hf) hσ (fun r m => f.map_smulₛₗ r m)

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  have hσ : Function.Bijective (cj s) := Function.Involutive.bijective (cj_cj s)
  let f : (Tw.sub s V) →ₛₗ[cj s] V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact finrank_eq_of_semi hσ f ⟨fun x y h => Subtype.ext (congrArg Subtype.val h), fun y => ⟨⟨Tw.mk s y.1, y.2⟩, rfl⟩⟩

theorem finrank_comap_of_le_range {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E →ₗ[ℂ] F) (he : Function.Injective e) (V : Submodule ℂ F) (hV : V ≤ LinearMap.range e) :
    Module.finrank ℂ (V.comap e) = Module.finrank ℂ V := by
  have h := (Submodule.equivMapOfInjective e he (V.comap e)).finrank_eq
  rwa [Submodule.map_comap_eq_self hV] at h

theorem finrank_EEC {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) :
    Module.finrank ℂ (EEC St Gd) = Module.finrank ℂ (goodSub St Gd) := by
  let f : EEC St Gd →ₛₗ[starRingEnd ℂ] goodSub St Gd :=
    { toFun := fun x => ⟨star (x : L2X St), (mem_EEC St Gd _).1 x.2⟩
      map_add' := fun x y => Subtype.ext ((conjL (muX St)).map_add _ _)
      map_smul' := fun c x => Subtype.ext ((conjL (muX St)).map_smulₛₗ c _) }
  refine finrank_eq_of_semi (Function.Involutive.bijective (fun z => Complex.conj_conj z)) f ⟨fun x y h => ?_, fun y => ?_⟩
  · exact Subtype.ext (star_injective (congrArg Subtype.val h))
  · refine ⟨⟨star (y : L2X St), ?_⟩, Subtype.ext (star_star _)⟩
    rw [mem_EEC, star_star]
    exact y.2

theorem finrank_of_evalTieT {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S}
    {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)}
    {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}
    (hE : EvalTieT M μ 𝓕 E St Gd ι t c) : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ E := by
  obtain ⟨_, _, j, _⟩ := hE
  rw [← finrank_EEC, ← j.finrank_eq]

theorem clauses {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) (n : ℝ)
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc)
    (h1 : ∀ e ∈ V, n * ‖sEEc e‖ ^ 2 = ‖e‖ ^ 2)
    (h2 : ∀ e ∈ V, ((Tw.out (s := s) (sEEc e) : HHX St) : L2X St) ∈ goodSub St Gd)
    (h3 : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ V) :
    (∀ e ∈ V, n * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ V, sEE e ∈ Sp.Rw) ∧
      Module.finrank ℂ Sp.Rw = Module.finrank ℂ V := by
  subst hSp
  obtain rfl := eq_of_heq h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  refine (finrank_twSub s ((goodSub St Gd).comap (HHX St).subtype)).trans ?_
  refine finrank_comap_of_le_range _ Subtype.val_injective _ ?_
  rw [Submodule.range_subtype]
  exact inf_le_left

end GlobalTheory.Mem.SJ.RowIso

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.SeeIsoRow

variable {D : D7} {S : D.what₂.Tau → SPar}

theorem sEEofTT_apply {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    sEEofTT M μ 𝓕 E St Gd ι t c T = conjHH St Gd (hE.choose_spec.2.choose T) := by
  unfold sEEofTT
  simp only [dif_pos hE]
  rfl

theorem norm_sq_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re := by
  have h := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h
  rw [h]
  exact (hE.choose_spec.2.choose_spec T).2

theorem eq_zero_of_sEEofTT {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA}
    {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c) (T : E)
    (h : ‖sEEofTT M μ 𝓕 E St Gd ι t c T‖ = 0) : T = 0 := by
  have h1 := congrArg norm (sEEofTT_apply hE T)
  rw [LinearIsometry.norm_map] at h1
  have h2 : ‖hE.choose_spec.2.choose T‖ = 0 := h1.symm.trans h
  exact (LinearEquiv.map_eq_zero_iff _).1 (norm_eq_zero.1 h2)

theorem seeIso_row : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (hK : X.LevelSubgroupCharacter) (Zs : DefSub A3.fam3.amb3) (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X)) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cS κS : ℝ) (uS : ℂ), R.toRealDat.IsModels → (R.toCx3 F).zs = Zs → F.Dc Zs = Dc → HEq (F.Sp Zs) (spOf (X := X) (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD pw bR) → HEq sEE sEEc → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS → ‖uS‖ = 1 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) ((uS * (κS : ℂ)) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩)) → (0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), ‖(κ' : ℂ) • (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS) ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖) → ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H), R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) → RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X Gd hK Zs Dc wdD pw bR sEE sEEc ι tS cS κS uS hM hzs hDc hSp hh hE _ hDef hK'
  subst hzs
  subst hDc
  have hSp' := eq_of_heq hSp
  have hHE := hM.HE
  have hle := (GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R.toRealDat hM).1 (R.toRealDat.levR F.lv2 true)
  have key : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 = cS * ‖x‖ ^ 2 := by
    intro x hx
    rw [norm_sq_sEEofTT hE]
    congr 1
    show (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2
    rw [← hHE.2.2]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (Tw.out x)
  have hex : ∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H)
      (hx : R.HE.e (Tw.out x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)),
      ‖(κ' : ℂ) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = ‖x‖ := by
    by_cases hc : 0 < cS
    · have hsp : 0 < Real.sqrt cS := Real.sqrt_pos.2 hc
      refine ⟨(Real.sqrt cS)⁻¹, inv_pos.2 hsp, fun x hx => ?_⟩
      have h1 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = Real.sqrt cS * ‖x‖ := by
        rw [← pow_left_inj₀ (norm_nonneg _) (mul_nonneg hsp.le (norm_nonneg _)) two_ne_zero, key x hx, mul_pow,
          Real.sq_sqrt hc.le]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hsp).le, h1, ← mul_assoc,
        inv_mul_cancel₀ hsp.ne', one_mul]
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have h2 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ ^ 2 ≤ 0 := by
        rw [key x hx]
        exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (sq_nonneg _)
      have h0 : ‖sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out x), hx⟩‖ = 0 :=
        pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
      have hT := eq_zero_of_sEEofTT hE _ h0
      have he0 : R.HE.e (Tw.out x) = 0 := congrArg Subtype.val hT
      have hx0 : Tw.out x = 0 := (map_eq_zero_iff _ hHE.1).1 he0
      rw [norm_smul, h0, mul_zero]
      show 0 = ‖Tw.out x‖
      rw [hx0, norm_zero]
  have hn := hK'.2 hex
  refine GlobalTheory.Mem.SJ.RowIso.clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs)
    hSp' ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => hn e he) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX X) =>
      ((Tw.out y : HHX X) : L2X X) ∈ goodSub X Gd) (hDef e he)).mpr ?_
    show (((uS * (κS : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) X Gd ι tS cS ⟨R.HE.e (Tw.out e), he⟩ : HHX X) : L2X X) ∈ goodSub X Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC X Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (GlobalTheory.Mem.SJ.RowIso.finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((GlobalTheory.Mem.SJ.RowIso.finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine GlobalTheory.Mem.SJ.RowIso.finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Twist.SeeIsoRow
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeEx

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Div.SeeIsoClose
theorem seeIso_of_seeEx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hSee
  exact GlobalTheory.Twist.SeeIsoRow.seeIso_row Q.Rl Q.F S.X S.G S.Y.hK P.Zs P.Dc Q.wdD
    (fun x => _root_.Formalism.IndefR.pwOf_alt S Q.hin (Q.wdD x)) Q.bR Q.sEE Q.sEEc Q.ιS Q.tS Q.cS Q.κS Q.uS
    Q.charW.base.models Q.zs Q.dc (Q.sp.trans Q.spPin) Q.sEEj (Q.seeEval hSee.2) Q.uS_norm Q.seeDef Q.seeK
end GlobalTheory.Div.SeeIsoClose
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeExStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  first | exact @_root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | exact _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | (intros; apply _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind
theorem small_along_alt : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact _root_.GlobalTheory.T.indefScale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlongStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

theorem _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.small_along_alt | exact _root_.GlobalTheory.Fc.Ind.small_along_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.small_along_alt <;> assumption)
end
end
end
