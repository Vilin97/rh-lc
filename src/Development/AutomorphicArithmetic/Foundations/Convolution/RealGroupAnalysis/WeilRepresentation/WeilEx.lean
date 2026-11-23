module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousFiniteAdeleEmbed
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousQuaternaryFormLeft
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaQuad
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenRel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Generic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.IdxEta
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContKer
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsBis
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsBis
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussOp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsRel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormRationalEmbed
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.AbMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActRat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierConstMul

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NormForm

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.normForm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (a : (A F)ˣ), (∃ s t : A F, (a : A F) = s ^ 2 - rt D.δ * t ^ 2) ↔ ∃ z : (A E)ˣ, ideleNorm F E z = a := by
  intro F E _ _ _ _ _ D a
  constructor
  · rintro ⟨s, t, h⟩
    have hm : D.mkE s t * D.bar (D.mkE s t) = am E (a : A F) := by rw [D.mkE_mul_bar, h]
    have hu : IsUnit (D.mkE s t * D.bar (D.mkE s t)) := by
      rw [hm]
      exact a.isUnit.map (am (F := F) E)
    obtain ⟨z, hz⟩ := isUnit_of_mul_isUnit_left hu
    refine ⟨z, Units.ext ?_⟩
    rw [D.coe_ideleNorm, hz, D.co_mkE, h]
    simp
  · rintro ⟨z, rfl⟩
    exact ⟨D.co z 0, D.co z 1, D.coe_ideleNorm z⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaEx

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.etaEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ η : HChar F, IsQuadCharOf E η ∧ (∀ a, η.1 a ^ 2 = 1) ∧ (∀ z : (A E)ˣ, η.1 (ideleNorm F E z) = 1) ∧
    ∀ a, η.1 a = 1 → ∃ (t : F) (z : (A E)ˣ), t ≠ 0 ∧ (a : A F) = rt t * (ideleNorm F E z : (A F)ˣ) := by
  intro F E _ _ _ _ _ D
  haveI : Algebra.IsQuadraticExtension F E :=
    ⟨by rw [Module.finrank_eq_card_basis D.b]; simp⟩
  have h0 : D.b 0 = 1 := D.b0
  have h1 : D.b 1 * D.b 1 = algebraMap F E D.δ := by
    rw [D.b1, ← pow_two, D.sq]
  obtain ⟨η, hq, hη⟩ := UpperTheory.ConvolutionTheory.R2.C.etaQuad F E
  have hone : ∀ a, GlobalTheory.IdeleNormChar.normSign E a = 1 → η.1 a = 1 := by
    intro a ha
    refine Units.ext ?_
    rw [hη a, ha]
    simp
  have hsign : ∀ a, η.1 a = 1 → GlobalTheory.IdeleNormChar.normSign E a = 1 := by
    intro a ha
    have h := hη a
    rw [ha] at h
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e
    · exact e
    · rw [e] at h
      norm_num at h
  have hmem : ∀ z : (A E)ˣ, ideleNorm F E z ∈ GlobalTheory.QuadSymbol.normGroup F E (A F) := by
    intro z
    obtain ⟨s, t, hst⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D (ideleNorm F E z)).2 ⟨z, rfl⟩
    exact (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).2 ⟨s, t, hst⟩
  refine ⟨η, hq, ?_, ?_, ?_⟩
  · intro a
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hη a]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;> rw [e] <;> simp
  · intro z
    exact hone _ (GlobalTheory.IdeleNormChar.normSign_of_mem E (hmem z))
  · intro a ha
    obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 (hsign a ha)
    obtain ⟨s, u, hsu⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form D.b h0 h1).1 ht
    obtain ⟨z, hz⟩ := (UpperTheory.ConvolutionTheory.R2.C.normForm F E D _).1 ⟨s, u, hsu⟩
    refine ⟨(t : F), z, t.ne_zero, ?_⟩
    rw [hz]
    have : a = GlobalTheory.QuadSymbol.toUnits F (A F) t * (a / GlobalTheory.QuadSymbol.toUnits F (A F) t) := by
      rw [mul_div_cancel]
    exact congrArg Units.val this
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Imports

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.cont :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), Continuous η → IsOm δ η Om →
    ∀ φ, Continuous fun p : G1 F × V4 F => (Om p.1 φ).1 p.2 := by
  intro F _ _ δ η Om hη hOm φ
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, v₀⟩
  obtain ⟨b, c, a, k, hb, hc, ha, hk, hev⟩ := near F
  set φ' : S4 F := Om g₀ φ with hφ'
  set φ'' : S4 F := Om (wW F)⁻¹ φ' with hφ''

  let H : G1 F × V4 F → G1 F := fun p => p.1 * g₀⁻¹
  have hH1 : H (g₀, v₀) = 1 := by simp [H]
  have hH : Tendsto H (𝓝 (g₀, v₀)) (𝓝 1) := by
    have : ContinuousAt H (g₀, v₀) := by
      have : Continuous H := continuous_fst.mul continuous_const
      exact this.continuousAt
    simpa [ContinuousAt, hH1] using this

  let f : G1 F × V4 F → ℂ := fun p =>
    ψ (b (H p) * q4 δ p.2) * (((η (a (H p)) : ℂˣ) : ℂ) * ((ab (a (H p)) ^ 2 : ℝ) : ℂ) *
      ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i))
  have hbH : ContinuousAt (fun p => b (H p)) (g₀, v₀) := by
    show Tendsto (fun p => b (H p)) _ (𝓝 (b (H (g₀, v₀))))
    rw [hH1]
    exact hb.tendsto.comp hH
  have hcH : ContinuousAt (fun p => c (H p)) (g₀, v₀) := by
    show Tendsto (fun p => c (H p)) _ (𝓝 (c (H (g₀, v₀))))
    rw [hH1]
    exact hc.tendsto.comp hH
  have haH : ContinuousAt (fun p => a (H p)) (g₀, v₀) := by
    show Tendsto (fun p => a (H p)) _ (𝓝 (a (H (g₀, v₀))))
    rw [hH1]
    exact ha.tendsto.comp hH
  have hf : ContinuousAt f (g₀, v₀) := by
    have hs : ContinuousAt (fun p : G1 F × V4 F => p.2) (g₀, v₀) := continuous_snd.continuousAt
    have hav : ContinuousAt (fun p => ((a (H p) : (A F)ˣ) : A F)) (g₀, v₀) :=
      Units.continuous_val.continuousAt.comp haH
    have h1 : ContinuousAt (fun p : G1 F × V4 F => ψ (b (H p) * q4 δ p.2)) (g₀, v₀) :=
      continuous_ψ.continuousAt.comp (hbH.mul ((continuous_quaternaryQuadraticForm δ).continuousAt.comp hs))
    have h2 : ContinuousAt (fun p : G1 F × V4 F => ((η (a (H p)) : ℂˣ) : ℂ)) (g₀, v₀) :=
      (Units.continuous_val.comp hη).continuousAt.comp haH
    have h3 : ContinuousAt (fun p : G1 F × V4 F => ((ab (a (H p)) ^ 2 : ℝ) : ℂ)) (g₀, v₀) :=
      Complex.continuous_ofReal.continuousAt.comp ((continuous_ab.continuousAt.comp haH).pow 2)
    have hvec : ContinuousAt (fun p : G1 F × V4 F => (fun i => (a (H p) : A F) * p.2 i : V4 F)) (g₀, v₀) := by
      refine continuousAt_pi.2 fun i => hav.mul ?_
      exact (continuous_apply i).continuousAt.comp hs
    have h4 : ContinuousAt (fun p : G1 F × V4 F =>
        ft4 δ (fun y => ψ (c (H p) * q4 δ y) * φ''.1 y) (fun i => (a (H p) : A F) * p.2 i)) (g₀, v₀) :=
      ContinuousAt.comp (f := fun p : G1 F × V4 F => (c (H p), (fun i => (a (H p) : A F) * p.2 i : V4 F)))
        (g := fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ''.1 y) p.2)
        (contKer F δ φ'').continuousAt (hcH.prodMk hvec)
    exact h1.mul ((h2.mul h3).mul h4)
  refine hf.congr ?_

  have hlev : ∀ᶠ h in 𝓝 (1 : G1 F), InfOne (k h) → Om (k h) φ' = φ' := by
    exact hk.eventually (level F δ η Om hOm φ')
  filter_upwards [hH.eventually (hev.and hlev)] with p hp
  obtain ⟨⟨hinf, hdec⟩, hl⟩ := hp
  have hg : p.1 = H p * g₀ := by simp [H]
  have hkey : Om p.1 φ = Om (nU (b (H p))) (Om (mD (a (H p))) (Om (wW F) (Om (nU (c (H p))) φ''))) := by
    rw [hg, map_mul, Module.End.mul_apply, ← hφ']
    conv_lhs => rw [hdec]
    simp only [map_mul, Module.End.mul_apply]
    rw [hl hinf]
  show f p = (Om p.1 φ).1 p.2
  rw [hkey, hOm.n, hOm.m, hOm.w]
  show _ = ψ _ * (_ * _ * ft4 δ (Om (nU (c (H p))) φ'').1 _)
  have : (Om (nU (c (H p))) φ'').1 = fun y => ψ (c (H p) * q4 δ y) * φ''.1 y := funext (hOm.n _ _)
  rw [this]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsGauss

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.opsGauss :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) →
    (∀ b : (A F)ˣ, IsIdx δ (b : A F) (((η b : ℂˣ) : ℂ) * (((ab b)⁻¹ ^ 2 : ℝ) : ℂ))) → Gauss O.N O.M O.W := by
  intro F _ _ δ η O hδ hη hidx t
  obtain ⟨b, hb⟩ : ∃ b : (A F)ˣ, b = -t⁻¹ := ⟨_, rfl⟩
  have hbc : -((t⁻¹ : (A F)ˣ) : A F) = (b : A F) := by simp [hb]
  have htb : -(((b⁻¹ : (A F)ˣ) : A F)) = (t : A F) := by simp [hb]
  rw [hbc, ← hb]
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  simp only [Module.End.mul_apply]
  have hL : (O.W (O.N (t : A F) (O.W φ))).1 v =
      ft4 δ (fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y) v := by
    rw [O.W_apply]
    congr 1
    funext y
    rw [O.N_apply, O.W_apply]
  have hR : (O.N (b : A F) (O.M b (O.W (O.N (b : A F) φ)))).1 v =
      ((η b : ℂˣ) : ℂ) * ((ab b ^ 2 : ℝ) : ℂ) * Pc δ (b : A F) φ.1 v := by
    rw [O.N_apply, O.M_apply, O.W_apply, (pcMem F δ).1]
    have : (fun y => (O.N (b : A F) φ).1 y) = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x :=
      funext fun y => O.N_apply _ _ _
    have h2 : (O.N (b : A F) φ).1 = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x := this
    rw [h2]
    ring
  have hG := gaussOp F δ hδ b _ (hidx b) φ v
  have hη2 : ((η b : ℂˣ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hη b)
    simpa using this
  have hab : ab b ≠ 0 := by
    have : 0 < ab b := (IdeleGroup.ideleModule F b).2
    exact this.ne'
  have habc : ((ab b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  have hfn : (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) =
      fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y := by
    funext y
    rw [← htb, neg_mul]
  rw [hfn] at hG
  rw [hL, hR, hG]
  push_cast
  field_simp
  rw [hη2]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.weilEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), St.WeilEx D := by
  intro F E _ _ _ _ _ _ _ D
  have hδ : D.δ ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro h
    have := D.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨η, hq, hsq, hn, hk⟩ := etaEx F E D
  obtain ⟨O⟩ := opsEx F D.δ η.1 hδ
  obtain ⟨Om, h1, h2, h3⟩ := chunk F _ O.N O.M O.W (opsRel F D.δ η.1 O hδ hsq)
    (opsGauss F D.δ η.1 O hδ hsq (idxEta F E D η.1 hsq hk)) (generic F)
  have hO : IsOm D.δ η.1 Om :=
    ⟨fun b φ v => h1 b ▸ O.N_apply b φ v, fun a φ v => h2 a ▸ O.M_apply a φ v, fun φ v => h3 ▸ O.W_apply φ v⟩
  obtain ⟨L, hL⟩ := UpperTheory.ConvolutionTheory.R2.D.lEx F E D
  exact ⟨{
    η := η, Om := Om, L := L, quad := hq, η_sq := hsq, η_norm := hn, Om_n := hO.n, Om_m := hO.m, Om_w := hO.w, L_apply := hL
    comm := UpperTheory.ConvolutionTheory.R2.D.comm F E D η.1 Om L hn hO.n hO.m hO.w hL
    th_Om := thOm F D.δ η.1 Om hδ hO
    th_L := fun γ φ => by
      rw [← UpperTheory.ConvolutionTheory.R2.D.thL F E D γ φ.1]
      exact congrArg Th (funext (hL _ φ))
    level := level F D.δ η.1 Om hO
    unr := fun φ => unrOf F _ (level F D.δ η.1 Om hO φ)
    cont := cont F D.δ η.1 Om η.2.1 hO }⟩
end
end
