module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSphericalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HeckeScalarDC

open GlobalTheory.HeckeScalarSph

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem dc_scalar_fin (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (s : SplitPlace L) (α : GAf L n) (hα : TrivOutside {s.v} α) (Rα : Finset (GAf L n))
    (hRα0 : (∀ γ ∈ Rα, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ Rα ∧ γ⁻¹ * x ∈ Umax L n) :
    ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      ∑ γ ∈ Rα, NG.rt L n γ f = c • f := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα hRα0
  have hRtriv : ∀ γ ∈ Rα, TrivOutside {s.v} γ := by
    intro γ hγ
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hRα0.1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ Rα, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ Rα, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩

      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _

      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b Rα (R b) hα hb (fun y hy => hRα0.2 y (conv.1 hy))
        (fun γ hγ => conv.2 (hRα0.1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [← e]
  rfl

theorem dc_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS s α hα ι R r h1 h2
  classical
  have hinj : Set.InjOn r R := by
    intro γ hγ δ hδ e
    have hx := h1 γ hγ
    have hU : (r γ)⁻¹ * r γ ∈ Umax L n := by rw [inv_mul_cancel]; exact one_mem _
    exact (h2 (r γ) hx).unique ⟨hγ, hU⟩ ⟨hδ, by rw [← e]; exact hU⟩
  have hA : ∀ γ ∈ R.image r, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    exact h1 δ hδ
  have hB : ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) →
      ∃! γ, γ ∈ R.image r ∧ γ⁻¹ * x ∈ Umax L n := by
    intro x hx
    obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h2 x hx
    refine ⟨r γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hy
    rw [hu δ ⟨hδ, ey⟩]
  obtain ⟨c, hc⟩ := dc_scalar_fin a S hS s α hα (R.image r) ⟨hA, hB⟩
  refine ⟨c, fun f hf hfix => ?_⟩
  rw [← hc f hf hfix, Finset.sum_image (fun γ hγ δ hδ e => hinj hγ hδ e)]

end GlobalTheory.HeckeScalarDC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalDoubleCosetSumScalarIrreducibleFixedStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

theorem _root_.GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.HeckeScalarDC.dc_scalar | exact GlobalTheory.HeckeScalarDC.dc_scalar | (intros; apply GlobalTheory.HeckeScalarDC.dc_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocal

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitFrameReps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pre_mul_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    Formalism.IndefR.principalLevelFrame.pre Ψ (Ψ.ψ x) = x :=
  Ψ.inj (Formalism.IndefR.principalLevelFrame.pre_spec Ψ (Ψ.into x))

theorem frame_reps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  intro D V n hF Ψ hΨ Pp hS d hd
  obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D Pp (GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS)
  have hv : Formalism.L2.NG.OverPl Pp s.v := by rw [← hs]; exact s.w_under
  have hrep : GlobalTheory.Hk3.rep V Pp d = hd.choose := by unfold GlobalTheory.Hk3.rep; rw [dite_eq_left hd]
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hRs, hR⟩ := hd.choose_spec
  rw [hrep]
  have hK : ∀ k, k ∈ GlobalTheory.HeckeScalarSph.locK n s.v ↔
      Ψ.ψ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} :=
    fun k => and_congr (hΨ.2 k) (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv k).symm
  have h1 : (1 : Formalism.L2.Theta.GA D V) ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
    have := (hK 1).1 (one_mem _)
    rwa [map_one] at this
  have hαG : α ∈ Formalism.L2.Theta.GfC V := by
    obtain ⟨γ, ⟨hγ, hx⟩, -⟩ := hR.2 α ⟨1, h1, 1, h1, by rw [one_mul, mul_one]⟩
    have := mul_mem (hR.1 γ hγ).1 hx.1.1
    rwa [mul_inv_cancel_left] at this
  obtain ⟨a, rfl⟩ := Ψ.onto α hαG
  have hpull : ∀ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k},
      ∃ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Ψ.ψ κ = k := by
    intro k hk
    obtain ⟨κ, rfl⟩ := Ψ.onto k hk.1.1
    exact ⟨κ, (hK κ).2 hk, rfl⟩
  refine ⟨s, a, hv, (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨-, k₁, hk₁, k₂, hk₂, eγ⟩ := hR.1 γ hγ
    obtain ⟨κ₁, hκ₁, rfl⟩ := hpull k₁ hk₁
    obtain ⟨κ₂, hκ₂, rfl⟩ := hpull k₂ hk₂
    refine ⟨κ₁, hκ₁, κ₂, hκ₂, ?_⟩
    rw [eγ, ← map_mul, ← map_mul, pre_mul_eq]
  · rintro x ⟨κ₁, hκ₁, κ₂, hκ₂, rfl⟩
    obtain ⟨γ, ⟨hγ, hγx⟩, hu⟩ := hR.2 (Ψ.ψ (κ₁ * a * κ₂)) ⟨Ψ.ψ κ₁, (hK _).1 hκ₁, Ψ.ψ κ₂, (hK _).1 hκ₂, by rw [map_mul, map_mul]⟩
    have hγG : γ ∈ Formalism.L2.Theta.GfC V := (hR.1 γ hγ).1
    have eγ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ γ) = γ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hγG
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · have : Ψ.ψ ((Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * (κ₁ * a * κ₂)) ∈
          {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
        rw [map_mul, map_inv, eγ]; exact hγx
      exact ((hK _).2 this).1
    · rintro δ ⟨hδ, hδx⟩
      refine hu δ ⟨hδ, ?_⟩
      have hδG : δ ∈ Formalism.L2.Theta.GfC V := (hR.1 δ hδ).1
      have eδ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ δ) = δ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hδG
      have hδT : TrivOutside {s.v} (Formalism.IndefR.principalLevelFrame.pre Ψ δ) := by
        refine (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv _).1 ?_
        rw [eδ]; exact hRs δ hδ
      have hT : TrivOutside {s.v} ((Formalism.IndefR.principalLevelFrame.pre Ψ δ)⁻¹ * (κ₁ * a * κ₂)) :=
        GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hδT)
          (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul hκ₁.2
            ((GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα)) hκ₂.2)
      have := (hK _).1 ⟨hδx, hT⟩
      rwa [map_mul, map_inv, eδ] at this

end GlobalTheory.SplitFrameReps
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  first | exact @GlobalTheory.SplitFrameReps.frame_reps | exact GlobalTheory.SplitFrameReps.frame_reps | (intros; apply GlobalTheory.SplitFrameReps.frame_reps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatch

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SummandEig

theorem irrScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.sphericalDoubleCosetSum_scalar_irreducible_fixed

theorem isoScalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := GlobalTheory.T.rightTranslationSum_scalar_isotypic

theorem frameReps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem cast_sum {D : D7} (M : MtFam D) (μ : D.what₂.Tup) {j k : ℕ} (e : j = k) (h1 : 1 ≤ k) (h2 : k ≤ D.R.m)
    (h1' : 1 ≤ j) (h2' : j ≤ D.R.m) (f' : D.what₂.Mt μ j) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf D.host.E D.R.nV)
    (c : ℂ) (h : ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ k h1 h2).real (e ▸ f')) = c • (M μ k h1 h2).real (e ▸ f')) :
    ∑ γ ∈ R, Formalism.L2.NG.rt D.host.E D.R.nV (r γ) ((M μ j h1' h2').real f') = c • (M μ j h1' h2').real f' := by
  subst e
  exact h

theorem extV_inf {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (y : (X.R.HV j t).H) {a b : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j)}
    (ha : a ∈ Formalism.L2.Theta.GinfC (Formalism.IndefR.Links.Vc D j)) (hb : b ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j)) :
    X.R.extV j t y (a * b) = (X.R.cV j).ρ a⁻¹ (X.R.extV j t y b) := by
  have hcv := (X.given.core.models.cV j).1
  have e0 : ∀ g, X.R.extV j t y g = (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) := fun g => rfl
  have e1 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict a = 1 := by
    apply Subtype.ext
    exact (MonoidHom.mem_ker (f := Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j))).1 ha
  refine (e0 (a * b)).trans (Eq.trans ?_ (congrArg ((X.R.cV j).ρ a⁻¹) (e0 b)).symm)
  have e2 : (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict (a * b) = (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict b := by
    rw [map_mul, e1, one_mul]
  have e3 : (X.R.cV j).ρ (a * b)⁻¹ = (X.R.cV j).ρ a⁻¹ := by
    rw [mul_inv_rev, map_mul, hcv _ (inv_mem hb), one_mul]
  have e4 : (X.R.cV j).ρ b⁻¹ = 1 := hcv _ (inv_mem hb)
  have e5 : ∀ x, (X.R.cV j).ρ b⁻¹ x = x := fun x => by rw [e4]; rfl
  have e6 := congr (congrArg DFunLike.coe e3) (congrArg ((X.R.HV j t).e y) e2)
  exact e6.trans (congrArg ((X.R.cV j).ρ a⁻¹) (e5 _)).symm

end GlobalTheory.SummandEig
end
end
