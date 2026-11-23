module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.AeInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CosetShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CorePt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ConjStep

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.conjStep :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (α : (A E)ˣ),
      Measurable (w1 W f φ (aE α)) → (∀ b g, w1 W f φ (aE α) (nU b * g) = w1 W f φ (aE α) g) → Integrable (iw (w1 W f φ (aE α))) M.ν →
      W1 W M f φ (aE α) = ((ab (ideleNorm F E α) : ℝ) : ℂ) * M.I0 fun g => Wf f (dM (ideleNorm F E α) * gl g) *
        hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
  intro F E _ _ _ _ _ _ _ D W M f φ α h1 h2 h3
  have hn : nu F (aE α) = ideleNorm F E α := by
    unfold nu
    congr 1
    exact Units.ext (by simp [aE, Matrix.det_fin_two])
  have h4 := ((UpperTheory.ConvolutionTheory.R2.inv F M _ h1 h2 h3).2 (ideleNorm F E α)).2
  have hab : ((ab (ideleNorm F E α) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F (ideleNorm F E α)).2.ne'
  have h5 : (fun g => w1 W f φ (aE α) (cD (ideleNorm F E α) g)) = fun g => Wf f (dM (ideleNorm F E α) * gl g) *
      hat (W.Om g φ).1 ![0, ((ideleNorm F E α : (A F)ˣ) : A F), D.co ((α⁻¹ : (A E)ˣ) : A E) 0, D.co ((α⁻¹ : (A E)ˣ) : A E) 1] := by
    funext g
    have e1 : gl (cD (ideleNorm F E α) g) * dM (ideleNorm F E α) = dM (ideleNorm F E α) * gl g := by
      generalize ideleNorm F E α = t
      refine Units.ext ?_
      show (cD t g).1 * (dM t).val = (dM t).val * g.1
      ext i j : 2
      fin_cases i <;> fin_cases j <;> simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    have e2 : W.Om (cD (ideleNorm F E α) g) (W.L (aE α) φ) = W.L (aE α) (W.Om g φ) := by
      have := LinearMap.congr_fun (W.comm (aE α) g) φ
      rw [hn] at this
      exact this.symm
    have e3 : D.mkE 1 0 = 1 := by simp [Dat.mkE]
    rw [w1, hn, e1, e2, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).aE, e3, mul_one, mul_one]
  rw [← h5, h4, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hab, one_mul]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ImportsAlt

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.core :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → W.η.UnrAt v → W.η.val v = -1 →
      ∀ (Wt : GL (Fin 2) (A F) → ℂ) (α β : ℂˣ), EigAt v {α, β} Wt → (∀ b g, Wt (gl (nU b) * g) = ψ (-b) * Wt g) → ∀ φ : S4 F, Std v φ.1 →
      Integrable (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) M.ν →
      ((ab (idl v ϖ ^ 2) : ℝ) : ℂ) * (M.I0 fun g => Wt (dM (idl v ϖ ^ 2) * gl g) *
          hat (W.Om g φ).1 ![0, ((idl v ϖ ^ 2 : (A F)ˣ) : A F), (((idl v ϖ)⁻¹ : (A F)ˣ) : A F), 0]) =
        (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * M.I0 fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
  intro F E _ _ _ _ _ _ _ D W M v ϖ hϖ hg hu hv Wt α β hB hN φ hφ hi
  have := M.prob
  have mp : ∀ p : IdeleGroup F, MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight p) (MeasurableEquiv.refl (G1 F))) M.ν M.ν :=
    fun p => (measurePreserving_mul_right (ideleMeasure F) p).prod (MeasurePreserving.id M.κ)
  have hk : ∀ᵐ x ∂M.ν, x.2 ∈ KK F :=
    Measure.quasiMeasurePreserving_snd.ae (show ∀ᵐ k ∂M.κ, k ∈ KK F from M.supp)
  unfold Meas.I0
  have e1 := (mp (idl v ϖ)⁻¹).integral_comp' (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0])
  have i1 := ((mp (idl v ϖ)⁻¹).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [← (mp (idl v ϖ)).integral_comp', ← integral_const_mul]
  refine (integral_congr_ae (hk.mono fun x hx => corePt F E D W v ϖ hϖ hg hu hv Wt α β hB hN φ hφ x.1 x.2 hx)).trans ?_
  refine (integral_add (hi.const_mul _) (i1.const_mul _)).trans ?_
  rw [integral_const_mul, integral_const_mul]
  erw [e1]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open UpperTheory.V.Af.Smo (Eig)

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfEig :
    ∀ (F : Type) [Field F] [NumberField F], UpperTheory.ConvolutionTheory.R2.Pp.WfEig F := by
  intro F _ _ f hf v B h g
  let W (b : A F) (y : GL (Fin 2) (v.adicCompletion F)) :=
    f (gl (nU b) * (g * finGL F 2 (locGL F 2 v y)))
  have hW (b : A F) : Eig v B (W b) := by
    simpa only [W, mul_assoc] using h (gl (nU b) * g)
  have hi (y : GL (Fin 2) (v.adicCompletion F)) :
      IntegrableOn (fun b => W b y * ψ b) (fundamentalSet F) (adeleMeasure F) :=
    intOn ((hf.1.comp (cont_n.mul continuous_const)).mul cont_ψ)
  change Eig v B (fun y => ∫ b in fundamentalSet F, W b y * ψ b ∂(adeleMeasure F))
  refine ⟨(h 1).card, fun y k hk => by simp only [fun b => (hW b).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hsupp := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm F v 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hsum (G : GL (Fin 2) (v.adicCompletion F) ⧸ GlobalTheory.LFun.KGL v (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c =
        ∑ c ∈ hsupp.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov F v) ϖ j c.out * G c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hsum]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have hb := (hW b).eig ϖ hϖ j hj y
  rw [hsum] at hb
  simp only [← mul_assoc, ← hb, Finset.sum_mul]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WfEig

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.wfEig :
    ∀ (K : Type) [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ), Continuous f → (∀ γ g, f (ratGL K 2 γ * g) = f g) →
      (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧ ∀ v B, EigAt v B f → EigAt v B (Wf f) := by
  intro K _ _ f hc hl
  exact ⟨(UpperTheory.ConvolutionTheory.R2.Pp.wfBasic K f ⟨hc, hl⟩).2.1, UpperTheory.ConvolutionTheory.R2.Pp.wfEig K f ⟨hc, hl⟩⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LiftRel

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem nu_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x y : GL (Fin 2) (A E)) :
    nu F (x * y) = nu F x * nu F y := by simp only [nu, map_mul]

private theorem nu_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by simp only [nu, map_one]

private theorem dM_mul' {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : dM (s * t) = dM s * dM t :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two])

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 :=
  Units.ext (by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [dM])

private theorem coordinate_embedNorm_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) = Pi.single 0 u := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have e : D.mkE u 0 = u • AdeleBaseChange.adeleBasis D.b 0 := by
    rw [AdeleBaseChange.adeleBasis_apply, D.b0, map_one, Algebra.smul_def, mul_one, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  funext i
  simp only [Dat.co, e, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_pi_single]

private theorem co_mkE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 0 = u := by rw [coordinate_embedNorm_zero]; simp

private theorem co_mkE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (u : A F) :
    D.co (D.mkE u 0) 1 = 0 := by rw [coordinate_embedNorm_zero]; simp

theorem UpperTheory.ConvolutionTheory.R2.H.liftRel :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h₀ : GL (Fin 2) (A E),
      ∀ᶠ v : P F in cofinite, W.η.UnrAt v → W.η.val v = -1 → ∀ α β : ℂˣ, π.HasSat v {α, β} → ∀ (ϖ : (Kv v)ˣ) (z : (A E)ˣ), IsU ϖ →
        (z : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 → ideleNorm F E z = idl v ϖ ^ 2 →
        WE D (lift W M f.1 φ) (aE z * h₀) = (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D (lift W M f.1 φ) h₀ ∧
          ∀ h, lift W M f.1 φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((α : ℂ) * β) ^ 2 * lift W M f.1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h₀
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hl : IsOpen {k : GL (Fin 2) (Af F) | ∀ g, f.1 (g * finGL F 2 k) = f.1 g} := by
    convert (π.cusp f hf).1.level using 1
    exact Set.ext fun k => ⟨fun a => Subtype.ext (funext a), fun a g => congrFun (congrArg Subtype.val a) g⟩
  let f₁ : GL (Fin 2) (A F) → ℂ := fun g => f.1 (g * dM (nu F h₀))
  have hc : Continuous f₁ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).1.comp (continuous_mul_const _)
  have hleft : ∀ γ g, f₁ (ratGL F 2 γ * g) = f₁ g := fun γ g => by
    simp only [f₁, mul_assoc]
    exact (π.cusp f hf).1.left γ _
  have hw : ∀ x, w1 W f.1 φ (x * h₀) = w1 W f₁ (W.L h₀ φ) x := fun x => funext fun g => by
    simp only [w1, Wf, f₁, nu_mul', dM_mul', map_mul, Module.End.mul_apply, mul_assoc]
  have hb : w1 W f.1 φ h₀ = fun g => Wf f₁ (gl g) * UpperTheory.ConvolutionTheory.R2.hat (W.Om g (W.L h₀ φ)).1 ![0, 1, 1, 0] := by
    rw [← one_mul h₀, hw, one_mul]
    funext g
    simp only [w1, nu_one', dM_one', map_one, mul_one, Module.End.one_apply]
  obtain ⟨hN, hE⟩ := wfEig F f₁ hc hleft
  filter_upwards [gdAe F D.δ hδ, (aeK F).2.1 (nu F h₀), (aeK F).2.2 f.1 hl, stdAe F (W.L h₀ φ)] with v hg hk hfix hstd
    hu hval α β hB ϖ z hϖ hz hn
  have hEig := UpperTheory.V.Af.Smo.eigOfSat F 2 π v _ hB f hf hfix
  refine ⟨?_, fun h => ?_⟩
  · rw [UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ, UpperTheory.ConvolutionTheory.R2.exp F E D W M π f hf φ hφ]
    obtain ⟨-, -, c1, c2, c3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ (aE z * h₀)
    obtain ⟨-, -, -, -, c4⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h₀
    rw [hw] at c1 c2 c3
    rw [hb] at c4
    have e1 : W1 W M f.1 φ (aE z * h₀) = W1 W M f₁ (W.L h₀ φ) (aE z) := by simp only [W1, hw]
    have hz' : ((z⁻¹ : (A E)ˣ) : A E) = D.mkE (((idl v ϖ)⁻¹ : (A F)ˣ) : A F) 0 := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hz]
      simp only [Dat.mkE, map_zero, zero_mul, add_zero, ← map_mul, Units.mul_inv, map_one]
    rw [e1, conjStep F E D W M f₁ _ z c1 c2 c3, hn, hz', co_mkE, co_mkE',
      core F E D W M v ϖ hϖ hg hu hval (Wf f₁) α β (hE v _ ((fixTr F v f.1 _ hk).2 _ hEig)) hN _ hstd c4]
    simp only [W1, hb]
  · rw [(UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf), hn]
    by_cases h0 : f.1 = 0
    · simp [UpperTheory.ConvolutionTheory.R2.lift, h0]
    · obtain ⟨g, hg0⟩ := Function.ne_iff.1 h0
      obtain ⟨R, -, -, hR⟩ := heckeExpl F v ϖ hϖ
      have h1 : f.1 (g * lc v (1 * dL ϖ ϖ)) = (α : ℂ) * β * f.1 (g * lc v 1) := (hR α β _ (hEig g) 1).2
      have h2 : g * Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v ϖ) * g :=
        Units.ext ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq.symm)
      rw [one_mul, map_one, mul_one, (lcLaws F v).2.2.2.2.1, h2, hω f hf] at h1
      rw [map_pow, Units.val_pow_eq_pow_val, mul_right_cancel₀ hg0 h1]
end
end
