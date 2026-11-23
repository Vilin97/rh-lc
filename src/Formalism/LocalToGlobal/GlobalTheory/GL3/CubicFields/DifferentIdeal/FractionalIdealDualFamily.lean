module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.SumEmbDualBasisComplex

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem liftM_coe_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : ((liftM M x : M) : ℂ) = x := by
  rw [liftM, dite_eq_left h]

theorem sum_emb_eq_trace_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (a : E) :
    ∑ i, emb i a = φ₀ (Algebra.trace K E a) := by
  letI : Algebra K ℂ := φ₀.toAlgebra
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  let f : ι → (E →ₐ[K] ℂ) := fun i => { emb i with commutes' := fun y => hres i y }
  have hfinj : Function.Injective f := fun i j h => hinj (RingHom.ext fun x => AlgHom.congr_fun h x)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hcard, AlgHom.card K E ℂ]⟩
  have htr := trace_eq_sum_embeddings ℂ (K := K) (L := E) (x := a)
  calc ∑ i, emb i a = ∑ i, f i a := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ a := hbij.sum_comp (fun σ => σ a)
    _ = φ₀ (Algebra.trace K E a) := htr.symm

theorem sum_emb_eq_trace (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (a : E) :
    ∑ i, liftM M (emb i a) = liftM M (φ₀ (Algebra.trace K E a)) := by
  have hsum := sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard a
  have hmem : φ₀ (Algebra.trace K E a) ∈ M := hsum ▸ M.sum_mem (fun i _ => hM i a)
  apply Subtype.ext
  rw [IntermediateField.coe_sum, liftM_coe_of_mem M hmem, ← hsum]
  exact Finset.sum_congr rfl fun i _ => liftM_coe_of_mem M (hM i a)

theorem sum_emb_dualBasis_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, emb i (e j) * emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j) =
      if i = k then 1 else 0 := by
  have hexp : ∀ x, emb k x = ∑ i', emb i' x * ∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j) := by
    intro x
    conv_lhs => rw [← ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e).sum_repr x]

    rw [map_sum]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      hres, ← sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => by ring
  have hLI : LinearIndependent ℂ (fun i => ((emb i : E →+* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun i => (emb i).toMonoidHom)
      (fun i j h => hinj (RingHom.ext fun x => DFunLike.congr_fun h x))
  rw [Fintype.linearIndependent_iff] at hLI
  have h := hLI (fun i' => (∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)) - if i' = k then 1 else 0) (by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, hexp x]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _) i
  rwa [sub_eq_zero] at h

theorem sum_emb_dualBasis (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, liftM M (emb i (e j)) *
        liftM M (emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j)) =
      if i = k then 1 else 0 := by
  have hc := sum_emb_dualBasis_complex K E φ₀ ι emb hinj hres hcard e i k
  apply Subtype.ext
  rw [IntermediateField.coe_sum]
  simp only [IntermediateField.coe_mul, liftM_coe_of_mem M (hM _ _)]
  rw [hc]
  split_ifs <;> simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.FractionalIdealDualFamily

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

lemma coe_lift_intermediate {M : IntermediateField ℚ ℂ} {z : ℂ} (h : z ∈ M) : ((liftM M z : M) : ℂ) = z := by
  unfold liftM
  rw [dite_eq_left h]

lemma lift_integral_mem_range (M : IntermediateField ℚ ℂ) [NumberField M] {z : ℂ} (hz : z ∈ M)
    (hi : IsIntegral ℤ z) : liftM M z ∈ (algebraMap (𝓞 M) M).range := by
  have hint : IsIntegral ℤ (liftM M z) := by
    rw [← isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars ℤ) Subtype.val_injective]
    have h1 : ((IntermediateField.val M).restrictScalars ℤ) (liftM M z) = z := coe_lift_intermediate hz
    rw [h1]
    exact hi
  exact ⟨⟨liftM M z, hint⟩, rfl⟩

theorem mem_mmR_of (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (v : ι → M)
    (hv : v ∈ mmR M emb I) :
    ∀ b ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range := by
  intro b hb
  have hι : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  obtain ⟨i0⟩ := hι
  have hφ : ∀ y, φ₀ y ∈ M := fun y => by rw [← hres i0 y]; exact hM i0 _
  have hb' : ∀ a ∈ (I : Submodule (𝓞 E) E), Algebra.trace K E (b * a) ∈ (algebraMap (𝓞 K) K).range := by
    intro a ha
    have := (FractionalIdeal.mem_dual hI).mp hb a ha
    simpa [Algebra.traceForm_apply] using this
  refine Submodule.span_induction (p := fun v _ => ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range) ?_ ?_ ?_ ?_ hv
  · rintro w ⟨a, ha, rfl⟩
    have : ∑ i, liftM M (emb i a) * liftM M (emb i b) = liftM M (φ₀ (Algebra.trace K E (a * b))) := by
      rw [← sum_emb_eq_trace K E φ₀ M ι emb hinj hres hcard hM]
      refine Finset.sum_congr rfl fun i _ => ?_
      apply Subtype.ext
      rw [IntermediateField.coe_mul, coe_lift_intermediate (hM i a), coe_lift_intermediate (hM i b), coe_lift_intermediate (hM i (a * b)), map_mul]
    simp only [this]
    obtain ⟨t, ht⟩ := hb' a ha
    apply lift_integral_mem_range M (hφ _)
    rw [mul_comm a b, ← ht]
    exact (t.isIntegral_coe).map φ₀.toIntAlgHom
  · simp
  · intro x y _ _ hx hy
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hx hy
  · intro c x _ hx
    simp only [Pi.smul_apply, Algebra.smul_def, mul_assoc, ← Finset.mul_sum]
    exact mul_mem ⟨c, rfl⟩ hx

lemma fractional_ideal_span_top (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    Submodule.span K ((I : Submodule (𝓞 E) E) : Set E) = ⊤ := by
  have hne : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h; apply hI; apply FractionalIdeal.coeToSubmodule_injective; simpa using h
  obtain ⟨a, haI, ha0⟩ := (Submodule.ne_bot_iff _).mp hne
  rw [eq_top_iff]
  intro x _
  obtain ⟨m, hm0, hmz⟩ := exists_integral_multiples ℤ ℚ ({x / a} : Finset E)
  have hw := hmz (x / a) (by simp)
  let w : 𝓞 E := ⟨m • (x / a), hw⟩
  have hwa : w • a ∈ (I : Submodule (𝓞 E) E) := Submodule.smul_mem _ w haI
  have hx : x = ((m : K)⁻¹) • (w • a) := by
    have hm : (m : E) ≠ 0 := by exact_mod_cast hm0
    rw [Algebra.smul_def, Algebra.smul_def]
    show x = algebraMap K E ((m : K)⁻¹) * ((m • (x / a)) * a)
    rw [map_inv₀, map_intCast, zsmul_eq_mul]
    field_simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hwa)

lemma fractional_ideal_dual_family (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∃ (n : ℕ) (g : Fin n → E) (f : Fin n → ((I : Submodule (𝓞 E) E).restrictScalars (𝓞 K) →ₗ[𝓞 K] 𝓞 K)),
      (∀ j, g j ∈ (I : Submodule (𝓞 E) E)) ∧
      ∀ y : (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K), (y : E) = ∑ j, f j y • g j := by
  set P := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have : Module.IsTorsionFree (𝓞 K) E := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K E
  have : Module.IsTorsionFree (𝓞 K) P := inferInstance
  have hfg : P.FG := (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars
  have : Module.Finite (𝓞 K) P := Module.Finite.iff_fg.mpr hfg
  have : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite (𝓞 K) P
  have : Module.Projective (𝓞 K) P := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) P
  refine ⟨n, fun i => (F (Pi.single i 1) : E), fun i => (LinearMap.proj i).comp G,
    fun i => (F (Pi.single i 1)).2, fun y => ?_⟩
  have e1 : F (G y) = y := by
    have := congrArg (fun φ => φ y) hFG
    simpa using this
  have e2 : y = ∑ i, ((LinearMap.proj i).comp G) y • F (Pi.single i 1) := by
    conv_lhs => rw [← e1]
    rw [LinearMap.pi_apply_eq_sum_univ F (G y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  conv_lhs => rw [e2]
  simp

lemma trace_dual_of_functional (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (P : Submodule (𝓞 K) E) {κ : Type} [Fintype κ] (e : Module.Basis κ K E) (he : ∀ l, e l ∈ P)
    (f : P →ₗ[𝓞 K] 𝓞 K) :
    ∃ b : E, ∀ y (hy : y ∈ P), Algebra.traceForm K E b y = algebraMap (𝓞 K) K (f ⟨y, hy⟩) := by
  let F : E →ₗ[K] K := ∑ l, algebraMap (𝓞 K) K (f ⟨e l, he l⟩) • e.coord l
  refine ⟨((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).symm F, fun y hy => ?_⟩
  rw [← LinearMap.BilinForm.toDual_def (traceForm_nondegenerate K E), LinearEquiv.apply_symm_apply]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image (e.repr y))
  have hc : ∀ l, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d * e.repr y l := by
    intro l
    obtain ⟨c, hc⟩ := hd (e.repr y l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
    exact ⟨c, by rw [hc]; exact Algebra.smul_def _ _⟩
  choose c hc using hc
  have hdy : (d : 𝓞 K) • (⟨y, hy⟩ : P) = ∑ l, c l • (⟨e l, he l⟩ : P) := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Submodule.coe_sum]
    conv_lhs => rw [← e.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← algebraMap_smul K (c l), hc l, ← algebraMap_smul K (d : 𝓞 K), smul_smul]
  have hf := congrArg (fun z => algebraMap (𝓞 K) K (f z)) hdy

  simp only [map_smul, map_sum, smul_eq_mul, map_mul] at hf
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 K) K), (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero d.2
  apply mul_left_cancel₀ hd0
  rw [hf]
  simp only [hc]
  rw [LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  ring

theorem mem_mmR_iff (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (v : ι → M) :
    v ∈ mmR M emb I ↔
      ∀ b ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range := by
  refine ⟨mem_mmR_of K E φ₀ M ι emb hinj hres hcard hM I hI v, fun hv => ?_⟩
  obtain ⟨i0⟩ : Nonempty ι := by rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hφ : ∀ y, φ₀ y ∈ M := fun y => by rw [← hres i0 y]; exact hM i0 _
  let ψ : ι → E →+* M := fun i => (emb i).codRestrict M (hM i)
  let φM : K →+* M := φ₀.codRestrict M hφ
  have hψ : ∀ i y, liftM M (emb i y) = ψ i y := fun i y =>
    Subtype.ext (by rw [coe_lift_intermediate (hM i y)]; rfl)
  have hψK : ∀ i (t : K) (y : E), ψ i (t • y) = φM t * ψ i y := fun i t y => by
    rw [Algebra.smul_def, map_mul]; congr 1; exact Subtype.ext (hres i t)
  set P := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K ((I : Submodule (𝓞 E) E) : Set E)
  let e : Module.Basis s K E := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, fractional_ideal_span_top K E I hI])
  letI : Fintype s := @Fintype.ofFinite _ (Module.Finite.finite_basis e)
  have he : ∀ l, e l ∈ P := fun l => by rw [Module.Basis.mk_apply]; exact hs l.2
  obtain ⟨n, g, f, hg, hfg⟩ := fractional_ideal_dual_family K E I
  choose b hb using fun j => trace_dual_of_functional K E P e he (f j)
  have hbd : ∀ j, b j ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) :=
    fun j => (FractionalIdeal.mem_dual hI).mpr fun a ha => ⟨f j ⟨a, ha⟩, (hb j a ha).symm⟩
  have hid : ∀ y (hy : y ∈ P), y = ∑ j, Algebra.traceForm K E (b j) y • g j := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : P) : E) from rfl, hfg ⟨y, hy⟩]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j y hy, algebraMap_smul]
  set e' := (Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e with he'
  have hbexp : ∀ j, b j = ∑ l, Algebra.traceForm K E (b j) (e l) • e' l := fun j => by
    conv_lhs => rw [← e'.sum_repr (b j)]
    simp [e']
  have key : ∀ i k, ∑ j, ψ i (b j) * ψ k (g j) = if k = i then 1 else 0 := by
    intro i k
    have hdb := sum_emb_dualBasis K E φ₀ M ι emb hinj hres hcard hM e k i
    simp only [hψ, ← he'] at hdb
    rw [← hdb]
    have h1 : ∀ l, ψ k (e l) = ∑ j, φM (Algebra.traceForm K E (b j) (e l)) * ψ k (g j) := fun l => by
      conv_lhs => rw [hid (e l) (he l)]

      rw [map_sum]; simp only [hψK]
    have h2 : ∀ j, ψ i (b j) = ∑ l, φM (Algebra.traceForm K E (b j) (e l)) * ψ i (e' l) := fun j => by
      conv_lhs => rw [hbexp j]

      rw [map_sum]; simp only [hψK]
    simp only [h1, h2, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  choose c hc using fun j => RingHom.mem_range.mp (hv (b j) (hbd j))
  have hv' : v = ∑ j, c j • (fun i => liftM M (emb i (g j))) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Algebra.smul_def, hc, hψ, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, key]
    simp
  rw [hv']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g j, hg j, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end
end
