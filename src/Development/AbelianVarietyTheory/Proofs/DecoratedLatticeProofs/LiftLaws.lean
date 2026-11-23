module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrExtract

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.FixedLevelIsolate

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

end GlobalTheory.FixedLevelIsolate

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalSourceLevelCharacter

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.SeeSaw.LocSrc

section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem valuation_det_of_mem_stabLat {Y : Type} [Fintype Y] [DecidableEq Y] {g h : GL Y k} (hh : h ∈ GlobalTheory.StepData.stabLat g) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  have h1 := valuation_det_of_mem_KO (GlobalTheory.StepData.mem_stabLat.1 hh)
  have e : Matrix.GeneralLinearGroup.det (g⁻¹ * h * g) = Matrix.GeneralLinearGroup.det h := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [e] at h1

theorem om_Phi {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j a : ℕ) (H : j + a = s) (hb : j + (a + 1) = s + 1)
    (x : ((S.T t).lev j (a + 1) hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) x.1 1 ((S.T t).Phi j a H) = (((S.T t).lev j (a + 1) hb).lam x : ℂ) • (S.T t).Phi j a H := by
  obtain ⟨e1, e2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev j (a + 1) hb).J := by rw [(e2 j (a + 1) hb).1]; exact x.2
  have L : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (L.1 j a H).1 ⟨x.1, hx⟩
  rw [e1, (e2 j (a + 1) hb).2 x.1 hx x.2] at h1
  exact h1

end Local

theorem seeSaw_local_sourceLevel_character : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → j ≤ G.s → ∀ (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j)), (ofSplit G.q).IsLoc (G.FY j b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (h, 1) (comb c.ψ _ _ (G.eg j) f) = (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT hj b hb x h hl f hf
  obtain ⟨μ', hT, hT'⟩ := hT
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  have H : j + a = G.s := by omega
  have H' : j + 1 + a = G.s + 1 := by omega
  have hm := G.hs
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ (c.V j) (c.V (j + 1)) (G.FY j (a + 1) hb) (G.FY (j + 1) a H')
    c.ψ G.S.ψ hc.std G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (a + 1) hb) (G.latY (j + 1) a H')).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1))
  have R : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  let Φ : SB (Matrix (XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1)) G.k) :=
    ⟨(G.S.T (Fin D.R.t)).Phi j a H, R.1 j a H⟩
  have e1 : Tm Φ = comb c.ψ _ _ (G.eg j) f := by
    rw [← hO O hO1]
    exact (G.eg_is j a H).2 Tm hTm O Φ hO1 rfl
  have hd := valuation_det_of_mem_stabLat ((R.2.2 j (a + 1) hb).2.2 x.2)
  have e2 : ((μ (j + 1))⁻¹ * μ'⁻¹) (Matrix.GeneralLinearGroup.det x.1) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, ← mul_inv, mul_comm, hT' _ hd, inv_one]
  have key := GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω (μ (j + 1))⁻¹ μ' (isComp_inv _ hS) hT _ _
    (G.FY j (a + 1) hb) (G.FY (j + 1) a H') Tm hTm h x.1 1 1 hl (isLoc_one _ _) Φ
    ((((G.S.T (Fin D.R.t)).lev j (a + 1) hb).lam x : ℂ) • Φ) (by
      rw [e2, inv_inv, Units.val_one, one_smul]
      exact (om_Phi G.S (Fin D.R.t) μ hμ hu j a H hb x).symm)
  rw [← e1, key, map_smul]

end GlobalTheory.SeeSaw.LocSrc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetLaw

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.SeeSaw.LocTarget

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y : Type} [Fintype Y] [DecidableEq Y] {S : HSp D} (F : GlobalTheory.LocMod.Frame k S.rank Y) : p.IsLoc F 1 1 := by
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero], ?_⟩
  rw [h1, Units.val_one, Matrix.mul_one, F.βγ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isComp_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]

theorem om_phi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j b : ℕ) (H : j + b = s) (hb : j + 1 + b = s + 1)
    (x : ((S.T t).lev (j + 1) b hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) 1 x.1 ((S.T t).Phi j b H) =
      ((((S.T t).lev (j + 1) b hb).lam x : ℂ))⁻¹ • (S.T t).Phi j b H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hL : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  obtain ⟨hJ, hl⟩ := h2 (j + 1) b hb
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev (j + 1) b hb).J := by rw [hJ]; exact x.2
  have := (hL.1 j b H).2 ⟨x.1, hx⟩
  rw [h1, hl x.1 hx x.2, Units.val_inv_eq_inv_val] at this
  exact this

end GlobalTheory.SeeSaw.LocTarget
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftLaws

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.RowLevel.Std

section
open GlobalTheory.SeeSaw.LocTarget

theorem std_target : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), IsStdChar D c.ψ (-1) → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → ∀ (b : ℕ) (hb : j + 1 + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev (j + 1) b hb).J) (h : GA D (c.V (j + 1))), (ofSplit G.q).IsLoc (G.FY (j + 1) b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (1, h) (comb c.ψ _ _ (G.eg j) f) = ((((G.S.T (Fin D.R.t)).lev (j + 1) b hb).lam x : ℂ))⁻¹ • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT b hb x h hx f hf
  have hs := G.hs
  have H : j + b = G.s := by omega
  obtain ⟨μT, hT, -⟩ := hT
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY j (b + 1) (by omega)) (G.FY (j + 1) b hb) c.ψ G.S.ψ
    hc G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (b + 1) (by omega)) (G.latY (j + 1) b hb)).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin b)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (b + 1))
  have hR : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  have e1 := (G.eg_is j b H).2 Tm hTm O ⟨_, hR.1 j b H⟩ hO1 rfl
  rw [← hO O hO1, ← e1, ← map_smul]
  refine GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω _ μT (isComp_inv _ hS) hT _ _ _ _ Tm hTm 1 1 h x.1
    (isLoc_one _ _) hx _ _ ?_
  rw [map_one, map_one, Units.val_one, one_smul, inv_inv]
  exact (om_phi G.S _ μ hμ hu j b H hb x).symm

end

section
open GlobalTheory.SeeSaw.LocSrc

theorem std_source : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), IsStdChar D c.ψ (-1) → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → j ≤ G.s → ∀ (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j)), (ofSplit G.q).IsLoc (G.FY j b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (h, 1) (comb c.ψ _ _ (G.eg j) f) = (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT hj b hb x h hl f hf
  obtain ⟨μ', hT, hT'⟩ := hT
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  have H : j + a = G.s := by omega
  have H' : j + 1 + a = G.s + 1 := by omega
  have hm := G.hs
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ (c.V j) (c.V (j + 1)) (G.FY j (a + 1) hb) (G.FY (j + 1) a H')
    c.ψ G.S.ψ hc G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (a + 1) hb) (G.latY (j + 1) a H')).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1))
  have R : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  let Φ : SB (Matrix (XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1)) G.k) :=
    ⟨(G.S.T (Fin D.R.t)).Phi j a H, R.1 j a H⟩
  have e1 : Tm Φ = comb c.ψ _ _ (G.eg j) f := by
    rw [← hO O hO1]
    exact (G.eg_is j a H).2 Tm hTm O Φ hO1 rfl
  have hd := valuation_det_of_mem_stabLat ((R.2.2 j (a + 1) hb).2.2 x.2)
  have e2 : ((μ (j + 1))⁻¹ * μ'⁻¹) (Matrix.GeneralLinearGroup.det x.1) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, ← mul_inv, mul_comm, hT' _ hd, inv_one]
  have key := GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω (μ (j + 1))⁻¹ μ' (isComp_inv _ hS) hT _ _
    (G.FY j (a + 1) hb) (G.FY (j + 1) a H') Tm hTm h x.1 1 1 hl (isLoc_one _ _) Φ
    ((((G.S.T (Fin D.R.t)).lev j (a + 1) hb).lam x : ℂ) • Φ) (by
      rw [e2, inv_inv, Units.val_one, one_smul]
      exact (om_Phi G.S (Fin D.R.t) μ hμ hu j a H hb x).symm)
  rw [← e1, key, map_smul]

end

section
open GlobalTheory.FixedLevelIsolate

theorem std_isolate : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), IsStdChar D c.ψ (-1) → v.Is → GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (f : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f → ∀ (i : Fin n), ∃ g, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) g ∧ comb c.ψ _ _ (v.eG j) f = comb c.ψ _ _ ((G i).eg j) g := by
  intro D c v n G hc _ hG j hj Ψ hΨ i
  have hI := GlobalTheory.DisjComb.main D c.ψ hc (c.V j) (c.V (j + 1))
  have hca : ∀ i', CombAt (· = (G i').q.v) ((G i').eg j) := fun i' =>
    eg_combAt (G i') j (by have := (G i').hs; omega)
  have hdisj : ∀ a b : Fin n, a ≠ b → ∀ p, p = (G a).q.v → ¬ p = (G b).q.v := fun a b hab p ha hb =>
    hab (hG.inj (ha.symm.trans hb))
  let g : Fin n → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((G a).eg j) f
  refine ⟨((List.finRange n).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) Ψ :=
      vac_mono (fun p hp => by rw [hp]; exact (hG.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin n), (∀ a ∈ l, a ≠ i) → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a t ih =>
        intro hl
        exact ((hI (· = (G a).q.v) (· = (G i).q.v) (hdisj a i (hl a (List.mem_cons_self ..)))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange n).mem_erase_iff.1 ha).1
  · rw [hG.eG j hj Ψ hΨ.1]
    exact foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ (List.mem_finRange i)

end

end GlobalTheory.RowLevel.Std

namespace GlobalTheory.RowLevel.Std
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

theorem loc_tgt {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (hc : IsStdChar D c.ψ (-1)) (hv : v.Is) {j : ℕ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om (c.V j) (c.V (j + 1))} (hom : IsWeilDatumO c.ψ _ _ χS χT om)
    (μ : ℕ → G.kˣ →* ℂˣ) (hμ : ∀ i, IsTame (μ i)) (hu : ∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x)
    (hS : (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)))
    (hT : ∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1)
    (b : ℕ) (hb : j + 1 + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev (j + 1) b hb).J) (h : GA D (c.V (j + 1)))
    (hx : (ofSplit G.q).IsLoc (G.FY (j + 1) b hb) h x.1) (f : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hf : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f) :
    om (1, h) (comb c.ψ _ _ (G.eg j) f) =
      ((((G.S.T (Fin D.R.t)).lev (j + 1) b hb).lam x : ℂ))⁻¹ • comb c.ψ _ _ (G.eg j) f :=
  std_target D c v G hc hv j χS χT om hom μ hμ hu hS hT b hb x h hx f hf

theorem seeSaw_local_sourceLevel_character {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (hc : IsStdChar D c.ψ (-1)) (hv : v.Is) {j : ℕ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om (c.V j) (c.V (j + 1))} (hom : IsWeilDatumO c.ψ _ _ χS χT om)
    (μ : ℕ → G.kˣ →* ℂˣ) (hμ : ∀ i, IsTame (μ i)) (hu : ∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x)
    (hS : (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)))
    (hT : ∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1)
    (hj : j ≤ G.s) (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j))
    (hx : (ofSplit G.q).IsLoc (G.FY j b hb) h x.1) (f : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hf : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f) :
    om (h, 1) (comb c.ψ _ _ (G.eg j) f) =
      (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f :=
  std_source D c v G hc hv j χS χT om hom μ hμ hu hS hT hj b hb x h hx f hf

theorem decomp {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v) (hG : GPin G) (j : ℕ)
    (k : GA D (c.V j)) (hk : k ∈ grpAt (c.V j) (· ∈ v.gP)) :
    ∃ h : Fin n → GA D (c.V j), (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
      k = ((List.finRange n).map h).prod := GlobalTheory.LevelCut.prod_local_parts D c v n G hG j k hk

theorem isolate {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v) (hc : IsStdChar D c.ψ (-1)) (hv : v.Is) (hG : GPin G)
    (j : ℕ) (hj : j + 1 < D.R.m) (f : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hf : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f) (i : Fin n) :
    ∃ g, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) g ∧ comb c.ψ _ _ (v.eG j) f = comb c.ψ _ _ ((G i).eg j) g :=
  std_isolate D c v n G hc hv hG j hj f hf i
end GlobalTheory.RowLevel.Std

namespace GlobalTheory.RowLevel.Std
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

theorem tgt_law {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v) (hc : IsStdChar D c.ψ (-1)) (hv : v.Is) (hG : GPin G)
    {j : ℕ} (hj : j + 1 < D.R.m) {χS χT : (AE D)ˣ →* Circle} {om : Om (c.V j) (c.V (j + 1))}
    (hom : IsWeilDatumO c.ψ _ _ χS χT om)
    (hch : ∀ i, ∃ μ : ℕ → (G i).kˣ →* ℂˣ, (∀ l, IsTame (μ l)) ∧
      (∀ l (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ l x = (G i).S.μ l x) ∧
      (ofSplit (G i).q).IsComp χS⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit (G i).q).IsComp χT μ' ∧ ∀ x : (G i).kˣ, valuation (G i).k (x : (G i).k) = 1 → μ' x * μ (j + 1) x = 1) :
    ∀ k ∈ v.JG (j + 1), ∃ a, a ≠ 0 ∧ GLam G (j + 1) k a ∧ ∀ f, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f →
      om (1, k) (comb c.ψ _ _ (v.eG j) f) = a⁻¹ • comb c.ψ _ _ (v.eG j) f := by
  intro k hk
  obtain ⟨hkg, hkJ⟩ := (hG.lev (j + 1) hj k).1 hk
  obtain ⟨h, hloc, hprod⟩ := decomp G hG (j + 1) k hkg
  have hs : ∀ i, j + 1 + ((G i).s - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  choose x hxM hxL using fun i => hloc i ((G i).s - j) (hs i)
  have hxJ : ∀ i, x i ∈ (((G i).S.T (Fin D.R.t)).lev (j + 1) ((G i).s - j) (hs i)).J := fun i => hkJ i _ _ _ (hxM i)
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → ℂ,
      ∀ i, lam i = ((((G i).S.T (Fin D.R.t)).lev (j + 1) ((G i).s - j) (hs i)).lam ⟨x i, hxJ i⟩ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨∏ i, lam i, ?_, ⟨fun i => (G i).s - j, hs, fun i => ⟨x i, hxJ i⟩, hxM, by simp only [hlam]⟩, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hlam]; exact Units.ne_zero _
  · intro f hf
    have key : ∀ i, om (1, h i) (comb c.ψ _ _ (v.eG j) f) = (lam i)⁻¹ • comb c.ψ _ _ (v.eG j) f := by
      intro i
      obtain ⟨g, hg, e⟩ := isolate G hc hv hG j hj f hf i
      obtain ⟨μ, h1, h2, h3, h4⟩ := hch i
      rw [e, hlam]
      exact loc_tgt (G i) hc hv hom μ h1 h2 h3 h4 _ (hs i) ⟨x i, hxJ i⟩ (h i) (hxL i) g hg
    have gen : ∀ l : List (Fin n), om (1, (l.map h).prod) (comb c.ψ _ _ (v.eG j) f) =
        (l.map fun i => (lam i)⁻¹).prod • comb c.ψ _ _ (v.eG j) f := by
      intro l
      induction l with
      | nil =>
        rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, one_smul, Prod.mk_one_one, map_one]
        rfl
      | cons i l ih =>
        have e : ((1 : GA D (c.V j)), ((i :: l).map h).prod) = (1, h i) * (1, (l.map h).prod) := by simp
        rw [e, map_mul, Module.End.mul_apply, ih, map_smul, key, smul_smul]
        simp [mul_comm]
    rw [hprod, gen, ← Finset.prod_inv_distrib, Fin.prod_univ_def]

theorem src_law {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v) (hc : IsStdChar D c.ψ (-1)) (hv : v.Is) (hG : GPin G)
    {j : ℕ} (hj : j + 1 < D.R.m) {χS χT : (AE D)ˣ →* Circle} {om : Om (c.V j) (c.V (j + 1))}
    (hom : IsWeilDatumO c.ψ _ _ χS χT om)
    (hch : ∀ i, ∃ μ : ℕ → (G i).kˣ →* ℂˣ, (∀ l, IsTame (μ l)) ∧
      (∀ l (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ l x = (G i).S.μ l x) ∧
      (ofSplit (G i).q).IsComp χS⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit (G i).q).IsComp χT μ' ∧ ∀ x : (G i).kˣ, valuation (G i).k (x : (G i).k) = 1 → μ' x * μ (j + 1) x = 1) :
    ∀ k ∈ v.JG j, ∃ a, a ≠ 0 ∧ GLam G j k a ∧ ∀ f, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f →
      om (k, 1) (comb c.ψ _ _ (v.eG j) f) = a • comb c.ψ _ _ (v.eG j) f := by
  intro k hk
  obtain ⟨hkg, hkJ⟩ := (hG.lev j (by omega) k).1 hk
  obtain ⟨h, hloc, hprod⟩ := decomp G hG j k hkg
  have hjs : ∀ i, j ≤ (G i).s := fun i => by have := (G i).hs; omega
  have hs : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := hjs i; omega
  choose x hxM hxL using fun i => hloc i ((G i).s + 1 - j) (hs i)
  have hxJ : ∀ i, x i ∈ (((G i).S.T (Fin D.R.t)).lev j ((G i).s + 1 - j) (hs i)).J := fun i => hkJ i _ _ _ (hxM i)
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → ℂ,
      ∀ i, lam i = ((((G i).S.T (Fin D.R.t)).lev j ((G i).s + 1 - j) (hs i)).lam ⟨x i, hxJ i⟩ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨∏ i, lam i, ?_, ⟨fun i => (G i).s + 1 - j, hs, fun i => ⟨x i, hxJ i⟩, hxM, by simp only [hlam]⟩, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [hlam]; exact Units.ne_zero _
  · intro f hf
    have key : ∀ i, om (h i, 1) (comb c.ψ _ _ (v.eG j) f) = lam i • comb c.ψ _ _ (v.eG j) f := by
      intro i
      obtain ⟨g, hg, e⟩ := isolate G hc hv hG j hj f hf i
      obtain ⟨μ, h1, h2, h3, h4⟩ := hch i
      rw [e, hlam]
      exact seeSaw_local_sourceLevel_character (G i) hc hv hom μ h1 h2 h3 h4 (hjs i) _ (hs i) ⟨x i, hxJ i⟩ (h i) (hxL i) g hg
    have gen : ∀ l : List (Fin n), om ((l.map h).prod, 1) (comb c.ψ _ _ (v.eG j) f) =
        (l.map lam).prod • comb c.ψ _ _ (v.eG j) f := by
      intro l
      induction l with
      | nil =>
        rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, one_smul, Prod.mk_one_one, map_one]
        rfl
      | cons i l ih =>
        have e : (((i :: l).map h).prod, (1 : GA D (c.V (j + 1)))) = (h i, 1) * ((l.map h).prod, 1) := by simp
        rw [e, map_mul, Module.End.mul_apply, ih, map_smul, key, smul_smul]
        simp [mul_comm]
    rw [hprod, gen, Fin.prod_univ_def]

end GlobalTheory.RowLevel.Std


open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel GlobalTheory.RowLevel.Std in
theorem GlobalTheory.RowLevel.Std.lift_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), IsStdChar D c.ψ (-1) → v.Is → GPin G → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → ∀ j σ (_ : j + 2 * σ + 2 = D.R.m), (∀ k ∈ v.JG (j + 1), ∃ a, a ≠ 0 ∧ GLam G (j + 1) k a ∧ ∀ f, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f → t.om j (1, k) (comb c.ψ _ _ (v.eG j) f) = a⁻¹ • comb c.ψ _ _ (v.eG j) f) ∧ (∀ k ∈ v.JG j, ∃ a, a ≠ 0 ∧ GLam G j k a ∧ ∀ f, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) f → t.om j (k, 1) (comb c.ψ _ _ (v.eG j) f) = a • comb c.ψ _ _ (v.eG j) f) ∧ (0 < σ → (∀ k ∈ v.JG (j + 1 + 1), ∃ a, a ≠ 0 ∧ GLam G (j + 1 + 1) k a ∧ ∀ f, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) f → t.om (j + 1) (1, k) (comb c.ψ _ _ (v.eG (j + 1)) f) = a⁻¹ • comb c.ψ _ _ (v.eG (j + 1)) f) ∧ ∀ k ∈ v.JG (j + 1), ∃ a, a ≠ 0 ∧ GLam G (j + 1) k a ∧ ∀ f, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) f → t.om (j + 1) (k, 1) (comb c.ψ _ _ (v.eG (j + 1)) f) = a • comb c.ψ _ _ (v.eG (j + 1)) f) := by
  intro D c v n G hc hv hG t ht hch j σ hσ
  have hm : j + 1 < D.R.m := by omega
  have wBF : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j σ hσ).χV (t.sBF j σ hσ).χW (t.om j) := by
    have := (t.sBF j σ hσ).weil
    rw [(ht.sBF j σ hσ).1] at this
    exact this
  have chBF : ∀ i, ∃ μ : ℕ → (G i).kˣ →* ℂˣ, (∀ l, IsTame (μ l)) ∧
      (∀ l (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ l x = (G i).S.μ l x) ∧
      (ofSplit (G i).q).IsComp (t.sBF j σ hσ).χV⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit (G i).q).IsComp (t.sBF j σ hσ).χW μ' ∧
        ∀ x : (G i).kˣ, valuation (G i).k (x : (G i).k) = 1 → μ' x * μ (j + 1) x = 1 := fun i => by
    obtain ⟨μ, h1, h2, h3, -⟩ := hch i
    exact ⟨μ, h1, h2, (h3 j σ hσ).1, (h3 j σ hσ).2⟩
  refine ⟨tgt_law G hc hv hG hm wBF chBF, src_law G hc hv hG hm wBF chBF, fun hσ0 => ?_⟩
  obtain ⟨σ', rfl⟩ : ∃ σ', σ = σ' + 1 := ⟨σ - 1, by omega⟩
  have hm' : j + 1 + 1 < D.R.m := by omega
  have wFB : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ' hσ).χV (t.sFB j σ' hσ).χW (t.om (j + 1)) := by
    have := (t.sFB j σ' hσ).weil
    rw [(ht.sFB j σ' hσ).1] at this
    exact this
  have chFB : ∀ i, ∃ μ : ℕ → (G i).kˣ →* ℂˣ, (∀ l, IsTame (μ l)) ∧
      (∀ l (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ l x = (G i).S.μ l x) ∧
      (ofSplit (G i).q).IsComp (t.sFB j σ' hσ).χV⁻¹ (μ (j + 1 + 1)) ∧
      ∃ μ', (ofSplit (G i).q).IsComp (t.sFB j σ' hσ).χW μ' ∧
        ∀ x : (G i).kˣ, valuation (G i).k (x : (G i).k) = 1 → μ' x * μ (j + 1 + 1) x = 1 := fun i => by
    obtain ⟨μ, h1, h2, -, h4⟩ := hch i
    exact ⟨μ, h1, h2, (h4 j σ' hσ).1, (h4 j σ' hσ).2⟩
  exact ⟨tgt_law G hc hv hG hm' wFB chFB, src_law G hc hv hG hm' wFB chFB⟩
end
end
