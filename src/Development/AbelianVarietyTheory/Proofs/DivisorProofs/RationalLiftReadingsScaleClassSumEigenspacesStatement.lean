module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfOrthogonalKer

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem adjoint_apply_of_orthogonal_ker {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℂ}
    (hu : u ∈ (LinearMap.ker T)ᗮ) (h : T (LinearMap.adjoint T (T u)) = l • T u) : LinearMap.adjoint T (T u) = l • u := by
  have hk : LinearMap.adjoint T (T u) - l • u ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, map_smul, h, sub_self]
  have hr : LinearMap.adjoint T (T u) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk'
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hk', inner_zero_left]
  have ho : LinearMap.adjoint T (T u) - l • u ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hr (Submodule.smul_mem _ l hu)
  have hz := Submodule.inner_right_of_mem_orthogonal hk ho
  rwa [inner_self_eq_zero, sub_eq_zero] at hz

theorem inner_apply_of_adjoint_eq {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {u : H} {l : ℝ}
    (h : LinearMap.adjoint T (T u) = (l : ℂ) • u) (w : H) : ⟪T u, T w⟫_ℂ = (l : ℂ) * ⟪u, w⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]

theorem conj_csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    starRingEnd ℂ (GlobalTheory.LiftLower.csumAt S ((starRingEnd ℂ).comp σ) f g) = GlobalTheory.LiftLower.csumAt S σ f g := by
  unfold GlobalTheory.LiftLower.csumAt

  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, RingHom.comp_apply, map_sum, map_mul,
  Complex.star_def, Complex.conj_conj]

end GlobalTheory.ConjScalar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem ker_le_span_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : X →ₛₗ[σ] H)
    (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W) (Rel : X → Y → Prop) (hex : ∀ x, ∃ y, Rel x y)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → jW y = T (j x)) :
    LinearMap.ker T ≤ Submodule.span ℂ (j '' {u | Rel u 0}) := by
  have hinj : Function.Injective jW := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h0
    exact (hind 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx
  choose f hf using hex
  have e : ∀ x, jW (f x) = T (j x) := fun x => hT x _ (hf x)
  let θ : X →ₗ[K] Y :=
    { toFun := f
      map_add' := fun x y => hinj (by rw [map_add (f := _), e, e, e, map_add (f := _), map_add (f := _)])
      map_smul' := fun a x => hinj (by rw [RingHom.id_apply, map_smulₛₗ, e, e, map_smulₛₗ, map_smul]) }
  refine (GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW T hsp hind fun x => (e x).symm).trans
    (Submodule.span_mono (Set.image_mono fun u hu => ?_))
  have h0 : f u = 0 := hu
  exact h0 ▸ hf u

theorem mem_orthogonal_of_le_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : Submodule ℂ H} {s : Set H}
    (h : N ≤ Submodule.span ℂ s) {v : H} (hv : ∀ u ∈ s, ⟪v, u⟫_ℂ = 0) : v ∈ Nᗮ := by
  refine Submodule.orthogonal_le h ((Submodule.mem_orthogonal' _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem u hu => exact hv u hu
  | zero => exact inner_zero_right _
  | add u u' _ _ h h' => rw [inner_add_right, h, h', add_zero]
  | smul a u _ h => rw [inner_smul_right, h, mul_zero]

theorem toF_mem {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  obtain ⟨f, hf, e⟩ : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : B.toF ℓ Z y = f := (congrArg B.S.basis.equivFun.symm e.symm).trans (B.S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem inner_eq_zero_of_mem_range_adjoint {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {a b : H}
    (ha : a ∈ LinearMap.range (LinearMap.adjoint T)) (hb : T b = 0) : ⟪a, b⟫_ℂ = 0 := by
  obtain ⟨w, rfl⟩ := ha
  rw [LinearMap.adjoint_inner_left, hb, inner_zero_right]

theorem mem_orthogonal_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ)
    (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W) (U : W ≃ₗᵢ[ℂ] W) (κ : ℂ) (g : W →ₗ[ℂ] W) (Rel : X → Y → Prop)
    (hex : ∀ x, ∃! y, Rel x y) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → U (jW y) = κ • g (th (j x))) {v : H} (hv : ∀ u, Rel u 0 → ⟪v, j u⟫_ℂ = 0) :
    v ∈ (LinearMap.ker th)ᗮ := by
  have hk := ker_le_span_of_rel σ j jW ((U.symm.toLinearEquiv.toLinearMap ∘ₗ (κ • g)) ∘ₗ th) Rel (fun x => (hex x).exists) hsp
    hind (fun x y h => U.toLinearEquiv.eq_symm_apply.2 (hT x y h))
  refine mem_orthogonal_of_le_span ((LinearMap.ker_le_ker_comp _ _).trans hk) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hv u hu

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem csum_eq_zero_of_adjoint (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : R.jV i t f ∈ LinearMap.range (LinearMap.adjoint (R.thG i t))) (hg : R.thG i t (R.jV i t g) = 0) :
    (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  have h3 : inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
    refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
    refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
      (h2 i t f) (h2 i t g)).trans ?_
    exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g
  exact (map_eq_zero _).1 (h3.symm.trans (inner_eq_zero_of_mem_range_adjoint _ hf hg))

end



theorem conjForms_mem_orthogonal_ker : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.LUnif → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ph : ℂ, ph ≠ 0 → (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ x, j ((A.fam.L i A.μ0).toF ℓ Z x) ∈ (LinearMap.ker th)ᗮ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hU gramR c0R c0L hT i σ c c₁ H j μ' η' th ph hph hex hC hD ℓ Z hH hE hZ x
  obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hC
  obtain ⟨-, κ, -, hκ⟩ := hall μ' η' c c₁ H j th hD
  have hsp := GlobalTheory.ConjSpan.span_conjForms R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.fam.L i A.μ0).S.basis
  refine mem_orthogonal_of_rel σ j ((R.FW i).j σ) th U κ (R.gW i σ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph) hex hsp (hU i σ).1
    hκ fun v hv => ?_
  have h0 : R.thG i A.μ0 (R.jV i A.μ0 v) = 0 :=
    (smul_eq_zero.1 ((map_zero _).symm.trans hv).symm).resolve_left hph
  refine (GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1 _ v).trans ?_
  exact (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt (A.fam.L i A.μ0) ℓ Z hH hE).2 v
    (fun y => csum_eq_zero_of_adjoint hM.HV hM.jV i A.μ0 (hZ _ (toF_mem _ ℓ Z y)) h0) σ x

end GlobalTheory.ConjScalar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearInjectiveOfIndep

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem semilinear_injective_of_indep {K L V W ι : Type} [Field K] [Field L] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module L W] {φ : K →+* L} (b : Module.Basis ι K V) (c : V →ₛₗ[φ] W)
    (h : LinearIndependent L fun a => c (b a)) : Function.Injective c := by
  refine (injective_iff_map_eq_zero c).2 fun v hv => ?_
  have hexp : c v = ∑ i ∈ (b.repr v).support, φ (b.repr v i) • c (b i) := by
    conv_lhs => rw [← b.linearCombination_repr v]

    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ c _ _
  have hz := linearIndependent_iff'.1 h (b.repr v).support (fun i => φ (b.repr v i)) (by rw [← hv, hexp])
  have hrepr : b.repr v = 0 := by
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    exact hne (φ.injective ((hz i (Finsupp.mem_support_iff.2 hne)).trans (map_zero φ).symm))
  exact b.repr.injective (hrepr.trans (map_zero _).symm)

theorem hkF_single_one {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) (h : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F h = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) := by
  simp only [GlobalTheory.Hk3.hkF]
  rw [Finsupp.sum_single_index, one_smul]
  exact zero_smul ℂ _

theorem hkF_transfer {D : D7} (V : HSp D) {K U W W' : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {φ σ : K →+* ℂ} (c₀ : U →ₛₗ[φ] W) (c₁ : U →ₛₗ[σ] W') (inj : Function.Injective c₀)
    (F : Bridge.Gf V → W) (F' : Bridge.Gf V → W') (hb : ∀ h, ∃ v, F h = c₀ v ∧ F' h = c₁ v)
    (P : Pl D.host.E) (d : List ℤ) (a : K) (e : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F = φ a • F) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F' = σ a • F' := by
  choose v hv using hb
  funext h
  have e' := congrFun e h
  rw [hkF_single_one, Pi.smul_apply] at e'
  rw [hkF_single_one, Pi.smul_apply]
  have key : ∑ γ ∈ GlobalTheory.Hk3.rep V P d, v (h * (finHom V).rangeRestrict γ) = a • v h := by
    apply inj

    rw [map_sum, map_smulₛₗ]
    simp only [← fun x => (hv x).1]
    exact e'
  simp only [fun x => (hv x).2]

  rw [← map_smulₛₗ, ← key, map_sum]

theorem eigF_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ a x, GlobalTheory.ConjScalar.EigK R i a x → GlobalTheory.ConjScalar.EigF R i (fun P d => σ (a P d)) (H.e (j x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ gramR c0R c0L hT i σ c c₁ H j hc a x hx
  have hind : LinearIndependent ℂ fun k => c0L i (bVV D.what₂.LL (lamV D i) k) :=
    (Formalism.IndefR.Bridge.FamTie.mapL hT i).2.1
  have inj : Function.Injective (c0L i) := semilinear_injective_of_indep (bVV D.what₂.LL (lamV D i)) (c0L i) hind
  intro P d hG hL
  have e := hx P d hG hL
  exact hkF_transfer (Vc D i) (c0L i) c₁ inj _ _ (hc.base x) P d (a P d) e

end GlobalTheory.ConjScalar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspaces

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar



theorem readings_scale_core : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  intro hH hCR D G _ _ Pl0 T0 A T _ R κ v₀ O F ph hC hψ hS fw hbar hio hU hpins i hom ℓ Z hHz hE hZ
  obtain ⟨gramR, c0R, c0L, tie⟩ := hC.fam.tie
  obtain ⟨hex, hconj, hbarσ⟩ := hCR D G Pl0 T0 A T R F κ v₀ O ph (GlobalTheory.Core5.of_core hC) hψ fw hbar hio hU hpins i hom
  have hph : ph ≠ 0 := by
    intro h0
    have h1 : ‖ph‖ = 1 := hom.2.1.2.2.2.2.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hcore : GlobalTheory.Hk3.Core R F := hC
  have key : ∀ σ : D.what₂.LL →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ a : Pl D.host.E → List ℤ → D.what₂.LL, ∃ l : ℝ, ∀ x x' y y',
      GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' →
      ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
    intro σ hσ a
    have hCA := hconj gramR c0R c0L tie σ hσ
    obtain ⟨μ', η', c, c₁, H, j, th, hD⟩ := hCA.2.1
    have hyp : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' := by
      obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hCA
      exact (hall μ' η' c c₁ H j th hD).1
    obtain ⟨ev, hev⟩ := GlobalTheory.T.conjugateDatumLift_jointEigenspace_into_one_part hH R F hcore gramR c0R c0L tie i σ c c₁ H j hσ μ' η' th hD hyp (fun P d => σ (a P d))
    obtain ⟨l, hl⟩ := hS gramR c0R c0L tie i σ hσ μ' η' c c₁ H j th hD ev
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    have hE' := eigF_conj R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1 a _ hx
    have hp := hev _ hE'
    have hperp := conjForms_mem_orthogonal_ker R hC.models hU gramR c0R c0L tie i σ c c₁ H j μ' η' th ph hph hex hCA hD ℓ Z hHz hE hZ x
    have hadj := adjoint_apply_of_orthogonal_ker th hperp (hl _ hp)
    refine (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hCA hD hy hy').trans ?_
    refine (inner_apply_of_adjoint_eq th hadj _).trans ?_
    rw [GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hC.models.jV gramR c0R c0L tie i σ c c₁ H j hD.2.2.1]
    rfl
  intro σ a
  by_cases hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ
  · exact key σ hσ a
  · obtain ⟨hσ', hbar'⟩ := hbarσ σ hσ
    obtain ⟨l, hl⟩ := key _ hσ' a
    refine ⟨l, fun x x' y y' hx hy hy' => ?_⟩
    rw [hbar' y y', hl x x' y y' hx hy hy', map_mul, Complex.conj_ofReal, conj_csumAt]

end GlobalTheory.ConjScalar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  first | exact @GlobalTheory.ConjScalar.readings_scale_core | exact GlobalTheory.ConjScalar.readings_scale_core | (intros; apply GlobalTheory.ConjScalar.readings_scale_core <;> assumption)
end
end
