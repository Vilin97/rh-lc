module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanImageOfForallHeightOneOverPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjoint

section

@[expose] public section

open GlobalTheory.Desc

open TensorProduct

namespace GlobalTheory.FlatSpanInter

theorem spanBy_algebraMap_eq {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] [Algebra R₁ F₁] (T : Set F₁) :
    spanBy (algebraMap R₁ F₁) T = (Submodule.span R₁ T : Set F₁) := by
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, by simp [Algebra.smul_def]⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, by simp [Algebra.smul_def]⟩

variable {R R₁ F F₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [CommRing F₁]
  [Algebra R R₁] [Algebra R F] [Algebra R₁ F₁] [Algebra R F₁] [IsScalarTower R R₁ F₁]

theorem smul_injective_tensor (hc₀ : Function.Injective (algebraMap R F)) {d : R} (hd : d ≠ 0)
    (x : R₁ ⊗[R] F) (hx : d • x = 0) : x = 0 := by
  set u : F := (algebraMap R F d)⁻¹
  have hu : u * algebraMap R F d = 1 :=
    inv_mul_cancel₀ (fun h => hd (hc₀ (by rw [h, map_zero])))
  have key : ∀ z : R₁ ⊗[R] F, LinearMap.lTensor R₁ (LinearMap.mulLeft R u) (d • z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.smul_def,
        ← mul_assoc, hu, one_mul]
    | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb]
  rw [← key x, hx, map_zero]

theorem free_injective (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁))
    {ι : Type} [Fintype ι] (v : ι → F) (hli : LinearIndependent R v) :
    Function.Injective ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set bB := Module.Basis.span hli
  set bb := Algebra.TensorProduct.basis R₁ bB
  have hval : ∀ j, ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) (bb j) = θ (v j) := by
    intro j
    simp [bb, bB, Algebra.TensorProduct.basis_apply, Module.Basis.span_apply, LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
  have e1 : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ
      ((Submodule.span R (Set.range v)).subtype.baseChange R₁)) y =
        ∑ j, algebraMap R₁ F₁ (bb.repr y j) * θ (v j) := by
    conv_lhs => rw [← bb.sum_repr y]

    simp only [map_sum, map_smul, hval, Algebra.smul_def]
  rw [hy] at e1
  set e := (Fintype.equivFin ι).symm
  have h0 := hLD _ (v ∘ e) (by
      intro r hr
      funext i
      exact Fintype.linearIndependent_iff.1 (hli.comp e e.injective) r
        (by simpa [Algebra.smul_def] using hr) i)
    (fun i => bb.repr y (e i)) (by
      rw [e1, ← Equiv.sum_comp e]
      rfl)
  have hr : bb.repr y = 0 := by
    ext j
    simpa using congrFun h0 (e.symm j)
  exact bb.repr.map_eq_zero_iff.1 hr

theorem liftBaseChange_injective (hc₀ : Function.Injective (algebraMap R F)) (θ : F →ₐ[R] F₁)
    (hLD : LinDisj (algebraMap R F) (algebraMap R₁ F₁) (θ : F →+* F₁)) :
    Function.Injective (LinearMap.liftBaseChange R₁ θ.toLinearMap) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set g : S → F := fun i => (i : R₁ × F).2
  obtain ⟨s, hli, hmax⟩ := exists_maximal_linearIndepOn R g
  have ha : ∀ i, ∃ a : R, a ≠ 0 ∧ a • g i ∈ Submodule.span R (g '' s) := by
    intro i
    by_cases hi : i ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩
    · exact hmax i hi
  choose a ha0 ha using ha
  set d := ∏ i, a i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => ha0 i)
  have hdg : ∀ i, d • g i ∈ Submodule.span R (Set.range fun j : s => g j) := by
    intro i
    rw [← Set.image_eq_range]
    obtain ⟨e, he⟩ : a i ∣ d := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    rw [he, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (ha i)
  haveI : Fintype s := Fintype.ofFinite s
  set B := Submodule.span R (Set.range fun j : s => g j)
  set y : R₁ ⊗[R] B := ∑ i : S, (i : R₁ × F).1 ⊗ₜ ⟨d • g i, hdg i⟩
  have hy : B.subtype.baseChange R₁ y = d • ∑ i ∈ S, i.1 ⊗ₜ i.2 := by
    rw [Finset.smul_sum, ← Finset.sum_coe_sort S]

    simp only [y, map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, g]
  have hz : ((LinearMap.liftBaseChange R₁ θ.toLinearMap) ∘ₗ (B.subtype.baseChange R₁)) y = 0 := by
    rw [LinearMap.comp_apply, hy, LinearMap.map_smul_of_tower, hx, smul_zero]
  have hy0 : y = 0 := free_injective θ hLD (fun j : s => g j) hli (by rw [hz, map_zero])
  exact smul_injective_tensor hc₀ hd _ (by rw [← hy, hy0, map_zero])

theorem spanBy_image_eq_map (θ : F →ₐ[R] F₁) (P : Submodule R F) :
    spanBy (algebraMap R₁ F₁) (θ '' P) =
      ((P.baseChange R₁).map (LinearMap.liftBaseChange R₁ θ.toLinearMap) : Set F₁) := by
  rw [spanBy_algebraMap_eq, Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  congr 2
  ext p
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory.FlatSpanInter

theorem GlobalTheory.Desc.spanBy_image_inter : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁]
    (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ →
    θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) →
    (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) →
    spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  intro R R₁ F F₁ _ _ _ _ _ ρ c₀ c₁ θ hρ hc₀ hcomp hLD M N hM0 hMa hMs hN0 hNa hNs
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R F := c₀.toAlgebra
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  letI : Algebra R F₁ := (c₁.comp ρ).toAlgebra
  haveI : IsScalarTower R R₁ F₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat R R₁ := hρ
  let θa : F →ₐ[R] F₁ := { θ with commutes' := fun r => RingHom.congr_fun hcomp r }
  let MS : Submodule R F :=
    { carrier := M, add_mem' := fun ha hb => hMa _ ha _ hb, zero_mem' := hM0,
      smul_mem' := fun r a ha => hMs r a ha }
  let NS : Submodule R F :=
    { carrier := N, add_mem' := fun ha hb => hNa _ ha _ hb, zero_mem' := hN0,
      smul_mem' := fun r a ha => hNs r a ha }
  have hinj := GlobalTheory.FlatSpanInter.liftBaseChange_injective (R₁ := R₁) hc₀ θa hLD
  have kI : spanBy c₁ (θ '' (M ∩ N)) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa (MS ⊓ NS)
  have kM : spanBy c₁ (θ '' M) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa MS
  have kN : spanBy c₁ (θ '' N) = _ := GlobalTheory.FlatSpanInter.spanBy_image_eq_map θa NS
  rw [kI, kM, kN, GlobalTheory.baseChange_inf, Submodule.map_inf _ hinj, Submodule.coe_inf]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjointStatement

section

@[expose] public section

open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) → (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) → spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  first | exact @GlobalTheory.Desc.spanBy_image_inter | exact GlobalTheory.Desc.spanBy_image_inter | (intros; apply GlobalTheory.Desc.spanBy_image_inter <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem height_comap_eq_one_of_flat_of_mem {R R₁ : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing R₁] [IsNoetherianRing R₁] (ρ : R →+* R₁) (hρ : ρ.Flat) {f : R} (hf : f ≠ 0)
    (q : Ideal R₁) [q.IsPrime] (hq : q.height = 1) (hfq : ρ f ∈ q) : (q.comap ρ).height = 1 := by
  letI := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  haveI : Algebra.HasGoingDown R R₁ := Algebra.HasGoingDown.of_flat
  haveI : (q.comap ρ).IsPrime := Ideal.comap_isPrime ρ q
  haveI : q.LiesOver (q.comap ρ) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.comap ρ) q
  have hle : (q.comap ρ).height ≤ 1 := by rw [← hq, h]; exact le_self_add
  refine le_antisymm hle ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro hb
  have : f ∈ q.comap ρ := hfq
  rw [hb, Ideal.mem_bot] at this
  exact hf this

end GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem spanBy_mono {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {T T' : Set F₁}
    (h : T ⊆ T') : spanBy c T ⊆ spanBy c T' := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact ⟨n, r, t, fun i => h (ht i), rfl⟩

theorem spanBy_sections_eq_of_flat : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin V₀ hV0 hVadd hVsmul _ W W₁
    htor hWcl hgauss
  have hW0 : ∀ p : Ideal R, p.IsPrime → f ∈ p → (0 : F) ∈ W p := fun p hp hfp => by
    obtain ⟨m, hm⟩ := htor p hp hfp 0
    simpa using hm
  set P := {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal} with hPdef
  have hP : P.Finite := GlobalTheory.finite_height_eq_one_mem hf

  have key : ∀ S : Finset (PrimeSpectrum R), (∀ p ∈ S, p ∈ P) →
      spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal}) =
        spanBy c₁ (θ '' V₀) ∩ {x | ∀ p ∈ S, x ∈ spanBy c₁ (θ '' W p.asIdeal)} := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => intro _; ext x; simp
    | insert a S ha ih =>
      intro hS
      have haP := hS a (Finset.mem_insert_self a S)
      obtain ⟨hadd, hsmul, -⟩ := hWcl a.asIdeal a.2 haP.1 haP.2
      have hSP : ∀ p ∈ S, p ∈ P := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have e : {u | u ∈ V₀ ∧ ∀ p ∈ insert a S, u ∈ W p.asIdeal} =
          {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} ∩ W a.asIdeal := by
        ext u; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
          forall_eq_or_imp]; tauto
      rw [e, GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint R R₁ F F₁ ρ c₀ c₁ θ hρ hc₀ hcomm hlin {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} (W a.asIdeal)
        ⟨hV0, fun p hp => hW0 p.asIdeal p.2 (hSP p hp).2⟩
        (fun a' ha' b hb => ⟨hVadd a' ha'.1 b hb.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).1 a' (ha'.2 p hp) b (hb.2 p hp)⟩)
        (fun r a' ha' => ⟨hVsmul r a' ha'.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).2.1 r a' (ha'.2 p hp)⟩)
        (hW0 a.asIdeal a.2 haP.2) hadd hsmul, ih hSP]
      ext x; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
        forall_eq_or_imp]; tauto
  have hS := key hP.toFinset (fun p hp => hP.mem_toFinset.mp hp)
  have e1 : {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p} =
      {u | u ∈ V₀ ∧ ∀ p ∈ hP.toFinset, u ∈ W p.asIdeal} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
    exact and_congr_right fun _ => ⟨fun h p hp => h p.asIdeal p.2 hp.1 hp.2,
      fun h p hp h1 hfp => h ⟨p, hp⟩ ⟨h1, hfp⟩⟩
  rw [e1, hS]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
  refine and_congr_right fun hx => ?_
  have hxr : x ∈ spanBy c₁ (Set.range θ) := spanBy_mono c₁ (Set.image_subset_range θ V₀) hx
  have hd : ∃ d : R₁, d ≠ 0 ∧ c₁ d * x ∈ spanBy c₁ (Set.range θ) := ⟨1, one_ne_zero, by simpa⟩
  constructor
  · intro h q hq hq1 hfq
    have h1 := height_comap_eq_one_of_flat_of_mem ρ hρ hf q hq1 hfq
    refine ((hgauss q hq hq1 hfq) x hd).mpr ⟨1, (Ideal.ne_top_iff_one q).mp hq.ne_top, ?_⟩
    simpa using h ⟨q.comap ρ, Ideal.comap_isPrime ρ q⟩ ⟨h1, hfq⟩
  · intro h p hp
    obtain ⟨hadd, hsmul, hinv⟩ := hWcl p.asIdeal p.2 hp.1 hp.2
    refine GlobalTheory.T.mem_span_image_of_forall_height_one_over_prime R R₁ F F₁ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin p.asIdeal p.2 hp.1 hp.2
      (W p.asIdeal) (htor p.asIdeal p.2 hp.2) hadd hsmul hinv x hxr fun q hq hq1 hfq hqp => ?_
    have := ((hgauss q hq hq1 hfq) x hd).mp (h q hq hq1 hfq)
    rwa [hqp] at this

end GlobalTheory.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.ringHomCoeffSpanSet_sections_flat_baseChange_normal : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  first | exact @GlobalTheory.Desc.spanBy_sections_eq_of_flat | exact GlobalTheory.Desc.spanBy_sections_eq_of_flat | (intros; apply GlobalTheory.Desc.spanBy_sections_eq_of_flat <;> assumption)
end
end
