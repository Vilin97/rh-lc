module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.BddArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupLevelOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArithmeticSubgroupsCommensurable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardOhatQuotientNatCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyBoundedEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartBoundOfSumBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyPartSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologySumBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicDoubleCosets
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelSubgroupIndexBoundOfCardOhat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AbsoluteBoundOfPartialBoundOfOrbitBound

section

@[expose] public section

open UpperTheory.V.Af.CohB in
theorem UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound :
    UpperTheory.V.Af.CohB.PartBound → UpperTheory.V.Af.CohB.OrbBound → UpperTheory.V.Af.CohB.AbsBound := by
  intro hP hO Γ Y _ _ hT hB
  obtain ⟨T, hT⟩ := hT
  choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)
  refine ⟨∑ t, cf t, ?_⟩
  intro X _ p hp D hD d ξ
  let r : MulAction.orbitRel.Quotient Γ Y → ↥T := fun q =>
    ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩
  let cl : X → ↥T := fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))
  have hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x := by
    intro γ x
    simp only [cl, hp]
    congr 1
    exact Quotient.sound ⟨γ, rfl⟩
  refine (hP Γ X ↥T cl hcl d ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1 := by
    rintro ⟨x, hx⟩
    change cl x = t at hx
    obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))
    refine ⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩
    rw [mul_smul]
    simp only at hh ⊢
    rw [hh]
    exact congrArg Subtype.val hx
  refine hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D
    (le_trans (Cardinal.mk_le_of_injective
      (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1}))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))) (hD t.1)) d ξ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiberCard

section

@[expose] public section

theorem UpperTheory.adelic_cohomology_fiber_card :
    UpperTheory.V.Af.CohB.FibCard := by
  intro G _ U U' h hne y
  set e := Subgroup.quotientEquivProdOfLE h with he
  have key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  have e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U') :=
    { toFun := fun x => (e x.1).2
      invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change e.symm (y, (e x).2) = x
        rw [← hx, ← key]
        exact e.symm_apply_apply x
      right_inv := by
        intro b
        change (e (e.symm (y, b))).2 = b
        rw [Equiv.apply_symm_apply] }
  rw [Cardinal.mk_congr e1]
  have : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hne
  rw [← Nat.cast_card]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicCohomologyFiniteOrbitBound

section

@[expose] public section

theorem UpperTheory.adelic_cohomology_finite_orbit_bound :
    UpperTheory.V.Af.CohB.FinOrbAbs := by
  classical
  intro G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩
  haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero
  haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU
  refine ⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image
    (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩
  obtain ⟨h, t, ht, k, hk, rfl⟩ := hT g
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ h⁻¹
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
  have huU : (((u : K) : G))⁻¹ ∈ U := U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)
  refine ⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩,
    _, huU, ?_⟩
  · simp [ht]
  · simp only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul]
    group
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsInjective

section

@[expose] public section

open scoped Matrix

theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CohomologyToCoinvariantsSurjective

section

@[expose] public section

open scoped Matrix in
theorem UpperTheory.cohomology_to_coinvariants_surjective :
    UpperTheory.V.Af.CohB.ToCoSurj := by
  intro Γ X Y _ _ _ p hp y h d ξ F
  choose c hc using h
  have hm : ∀ x, c x • x ∈ UpperTheory.V.Af.CohB.fib p hp y := fun x => by
    change p (c x • x) = y
    rw [hp, hc]
  have key : ∀ (g g' : Γ) (z z' : ↥(UpperTheory.V.Af.CohB.fib p hp y)), g⁻¹ • z.1 = g'⁻¹ • z'.1 →
      ξ g *ᵥ (ξ g'⁻¹ *ᵥ F.1 g' z') = F.1 g z := by
    intro g g' z z' hz
    have hz' : z.1 = (g * g'⁻¹) • z'.1 := by rw [mul_smul, ← hz, smul_inv_smul]
    have hs : g * g'⁻¹ ∈ MulAction.stabilizer Γ y := by
      have h1 : p z.1 = y := z.2
      have h2 : p z'.1 = y := z'.2
      rw [hz', hp, h2] at h1
      exact h1
    have h3 := congrFun (F.2 ⟨_, hs⟩ g') z
    have h4 : (⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z = z' := by
      apply Subtype.ext
      change (g * g'⁻¹)⁻¹ • z.1 = z'.1
      rw [hz', inv_smul_smul]
    change F.1 (g * g'⁻¹ * g') z = ξ (g * g'⁻¹) *ᵥ F.1 g' ((⟨_, hs⟩ : ↥(MulAction.stabilizer Γ y))⁻¹ • z) at h3
    rw [h4, inv_mul_cancel_right] at h3
    rw [h3, map_mul, Matrix.mulVec_mulVec]
  refine ⟨fun x => ξ (c x)⁻¹ *ᵥ F.1 (c x) ⟨c x • x, hm x⟩, ?_⟩
  apply Subtype.ext
  funext g z
  rw [UpperTheory.V.Af.CohB.toCo_apply]
  exact key g _ z _ (by simp)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitBoundOfShapiroFunctorial

section

@[expose] public section

theorem UpperTheory.orbit_bound_of_shapiro_functorial :
    UpperTheory.V.Af.CohB.ShapiroFun → UpperTheory.V.Af.CohB.OrbBound := by
  intro h Γ Y _ _ y hB
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, ?_⟩
  intro X _ p hp hsurj D hD d ξ
  rw [h Γ X Y p hp y hsurj d ξ]
  refine (hc _).trans ?_
  have h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D := hD
  have hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y) :=
    Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt Cardinal.natCast_lt_aleph0)
  have hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) =
      Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d := by
    change Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _
    rw [rank_pi]
    simp only [rank_fun', Fintype.card_fin]
    rw [Cardinal.sum_const']
  rw [hr]
  push_cast
  rw [mul_assoc]
  gcongr
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ShapiroFunctorialOfCoinductionBijective

section

@[expose] public section

open CategoryTheory UpperTheory.V.Af.CohB in
theorem UpperTheory.shapiro_functorial_of_coinduction_bijective :
    UpperTheory.V.Af.CohB.ToCoInj → UpperTheory.V.Af.CohB.ToCoSurj → UpperTheory.V.Af.CohB.ShapiroFun := by
  intro hi hs Γ X Y _ _ _ p hp y hy d ξ
  let e := LinearEquiv.ofBijective (toCo p hp y ξ) ⟨hi Γ X Y p hp y hy d ξ, hs Γ X Y p hp y hy d ξ⟩
  have he : ∀ g : Γ, e.toLinearMap ∘ₗ funRep X ξ g =
      Representation.coind (MulAction.stabilizer Γ y).subtype (fibRep p hp y ξ) g ∘ₗ e.toLinearMap := by
    intro g
    refine LinearMap.ext fun f => Subtype.ext (funext fun h => funext fun x => ?_)
    change funRep X ξ h (funRep X ξ g f) x.1 = funRep X ξ (h * g) f x.1
    rw [map_mul]
    rfl
  let i : Rep.of (funRep X ξ) ≅ Rep.coind (MulAction.stabilizer Γ y).subtype (Rep.of (fibRep p hp y ξ)) :=
    Rep.mkIso (Representation.Equiv.mk e he)
  unfold totCoh
  congr 1
  funext q
  exact (((groupCohomology.functor ℂ Γ q).mapIso i) ≪≫
    groupCohomology.coindIso (Rep.of (fibRep p hp y ξ)) q).toLinearEquiv.rank_eq
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CohBoundFree

section

@[expose] public section

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.CuspRep CategoryTheory UpperTheory.V.Af UpperTheory.V.Af.CohB

@[reducible] private def act {G H : Type} [Group G] [Group H] (ι : H →* G) (Γ : Subgroup H) (U : Subgroup G) :
    MulAction ↥Γ (G ⧸ U) := MulAction.compHom _ (ι.comp Γ.subtype)

private theorem gen (hE : BddEquiv) (hA : AbsBound) (hF : FibCard) {G H : Type} [Group G] [Group H] (ι : H →* G)
    (Γ : Subgroup H) (U : Subgroup G) (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ u ∈ U, g = ι γ * t * u)
    (S : G → Subgroup H) (hS : ∀ g γ, γ ∈ S g ↔ g⁻¹ * ι γ * g ∈ U) (hB : ∀ g, Bdd ↥(Γ ⊓ S g)) :
    ∃ c : ℕ, ∀ U' : Subgroup G, U' ≤ U → U'.relIndex U ≠ 0 → ∀ D : ℕ, U'.relIndex U ≤ D →
      ∀ (d : ℕ) (ξ : ↥Γ →* Matrix (Fin d) (Fin d) ℂ),
        totCoh (Rep.of (@funRep ↥Γ _ (G ⧸ U') (act ι Γ U') d ξ)) ≤ (c * D * d : ℕ) := by
  classical
  letI := act ι Γ U
  have hsm : ∀ (γ : ↥Γ) (g : G), γ • (g : G ⧸ U) = ((ι γ.1 * g : G) : G ⧸ U) := fun _ _ => rfl
  obtain ⟨T, hT'⟩ := hT
  obtain ⟨c, hc⟩ := hA ↥Γ (G ⧸ U)
    ⟨T.image (↑), fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨γ, hγ, t, ht, u, hu, rfl⟩ := hT' g
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, Finset.mem_image.2 ⟨t, ht, ?_⟩⟩
      rw [hsm, QuotientGroup.eq]
      simpa [mul_assoc] using hu⟩
    (fun y => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      have e : MulAction.stabilizer ↥Γ (g : G ⧸ U) = (Γ ⊓ S g).subgroupOf Γ := by
        ext γ
        rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hS,
          mul_assoc]
        exact ⟨fun h => ⟨γ.2, h⟩, fun h => h.2⟩
      exact hE ↥(Γ ⊓ S g) _
        ⟨((MulEquiv.subgroupCongr e).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm⟩ (hB g))
  refine ⟨c, fun U' hle h0 D hD d ξ => ?_⟩
  letI := act ι Γ U'
  exact hc (G ⧸ U') (Subgroup.quotientMapOfLE hle)
    (fun γ x => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rfl) D
    (fun y => by rw [hF _ _ _ hle h0 y]; exact_mod_cast hD) d ξ

private theorem levelRep_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (Γ : Subgroup (GL (Fin n) F))
    (U : Subgroup (GL (Fin n) (Af F))) {d : ℕ} (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    levelRep Γ U ξ = @funRep ↥Γ _ (GL (Fin n) (Af F) ⧸ U) (act (ratAf F n) Γ U) d (ξ.comp Γ.subtype) := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun f => funext fun x => ?_
  change ξ γ *ᵥ f ((ratAf F n γ.1)⁻¹ • x) = ξ γ *ᵥ f ((ratAf F n (γ.1)⁻¹) • x)
  rw [map_inv]

private theorem cohBound_of (hE : BddEquiv) (hA : AbsBound) (hF : FibCard)
    (hO : FinOrbAbs) (hI : KLevIdx) (hD : FinDC) (h1 : ArithOne) (hC : ArithComm) :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) := by
  intro F _ _ hF' n Γ hΓ
  obtain ⟨c, hc⟩ := gen hE hA hF (ratAf F n) Γ (KLev F n 3)
    (hO _ _ (ratAf F n) Γ (KLev F n 3) (KLev F n 1) hΓ (hI F n 3 (by norm_num)).1 (hD F n))
    (fun g => arith g (KLev F n 3)) (fun g γ => mem_arith) fun g => (bddArith F hF' n _
      (h1 F n ▸ hC F n Γ hΓ g _ (by apply isOpen_KLev; norm_num) (by apply isCompact_KLev; norm_num)))
  refine ⟨c * 3 ^ (Module.finrank ℚ F * (n * n)), Module.finrank ℚ F * (n * n), fun M hM d ξ => ?_⟩
  have hle : KLev F n (3 * M) ≤ KLev F n 3 := KLev_le_of_dvd (dvd_mul_right 3 M)
  have hle1 : KLev F n 3 ≤ KLev F n 1 := KLev_le_of_dvd (one_dvd 3)
  obtain ⟨hi0, hi⟩ := hI F n (3 * M) (by omega)
  have hr0 : (KLev F n (3 * M)).relIndex (KLev F n 3) ≠ 0 := fun h => hi0 (Subgroup.relIndex_eq_zero_of_le_right hle1 h)
  have hr : (KLev F n (3 * M)).relIndex (KLev F n 3) ≤ (3 * M) ^ (Module.finrank ℚ F * (n * n)) :=
    (Subgroup.relIndex_le_of_le_right hle1 hi0).trans hi
  have key := hc _ hle hr0 _ hr d (ξ.comp Γ.subtype)
  rw [← levelRep_eq] at key
  have e : c * 3 ^ (Module.finrank ℚ F * (n * n)) * M ^ (Module.finrank ℚ F * (n * n)) * d =
      c * (3 * M) ^ (Module.finrank ℚ F * (n * n)) * d := by rw [mul_pow, mul_assoc c]
  rw [e]
  exact key

theorem UpperTheory.V.Af.cohBoundFree :
    ∀ (F : Type) [Field F] [NumberField F], (IsTotallyComplex F ∨ IsTotallyReal F) → ∀ (n : ℕ) (Γ : Subgroup (GL (Fin n) F)),
      Γ.FiniteIndex → ∃ c A : ℕ, ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
        cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ) :=
  cohBound_of UpperTheory.cohomology_bounded_equiv
    (UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound (UpperTheory.cohomology_part_bound_of_sum_bound UpperTheory.cohomology_sum_bound UpperTheory.cohomology_part_split) (UpperTheory.orbit_bound_of_shapiro_functorial (UpperTheory.shapiro_functorial_of_coinduction_bijective UpperTheory.cohomology_to_coinvariants_injective UpperTheory.cohomology_to_coinvariants_surjective)))
    UpperTheory.adelic_cohomology_fiber_card UpperTheory.adelic_cohomology_finite_orbit_bound (UpperTheory.level_subgroup_index_bound_of_card_ohat UpperTheory.card_ohat_quotient_natCast) UpperTheory.finite_adelic_double_cosets UpperTheory.arithmetic_subgroup_level_one UpperTheory.arithmetic_subgroups_commensurable
end
end
