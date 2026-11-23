module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitOrbitsStableLatticesSeparableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibresStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjectionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerRelIndexIntUnitsNeZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticeOrbitCountEqSumOrbitsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairOrbitsFiniteAndCardProdStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroup

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩

theorem stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩

end GlobalTheory.UnitLemma
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroupStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup : ∀ (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A] (g : A) (L : stLat O E g), MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  first | exact @GlobalTheory.UnitLemma.stabilizer_le_intUnits | exact GlobalTheory.UnitLemma.stabilizer_le_intUnits | (intros; apply GlobalTheory.UnitLemma.stabilizer_le_intUnits <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticePairRelIndexIntegralUnits

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.PairStab

open GlobalTheory.UnitLemma Polynomial

theorem relIndex_prod_prod {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by
  have h : (H₁.prod H₂).subgroupOf (K₁.prod K₂) =
      ((H₁.subgroupOf K₁).prod (H₂.subgroupOf K₂)).comap (K₁.prodEquiv K₂).toMonoidHom := by
    ext x
    rfl
  unfold Subgroup.relIndex
  rw [h, Subgroup.index_comap_of_surjective _ (K₁.prodEquiv K₂).surjective, Subgroup.index_prod]

section

variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]

theorem intUnits_prod_eq :
    intUnits O (A₁ × A₂) = ((intUnits O A₁).prod (intUnits O A₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
  tauto

variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]

theorem stabilizer_latPair_eq (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂) :
    MulAction.stabilizer (A₁ × A₂)ˣ y = ((MulAction.stabilizer A₁ˣ y.1).prod
      (MulAction.stabilizer A₂ˣ y.2)).comap (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  rw [MulAction.mem_stabilizer_iff, latPair_smul, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Prod.ext_iff

end

theorem stabilizer_pair_relIndex : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ y h₁ h₂
  rw [stabilizer_latPair_eq, intUnits_prod_eq]
  refine ⟨Subgroup.comap_mono (fun t ht => ⟨h₁ ht.1, h₂ ht.2⟩), ?_⟩
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod_prod]

end GlobalTheory.UnitLemma.PairStab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticePairRelIndexIntegralUnitsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  first | exact @GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | exact GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex | (intros; apply GlobalTheory.UnitLemma.PairStab.stabilizer_pair_relIndex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnits

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem latProj_smul (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) :
    latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  rw [latPair_smul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).comap (LinearMap.inl O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.fst A₁ A₂) t : A₁ˣ) : A₁) ((M : Submodule O (A₁ × A₂)).comap (LinearMap.inl O A₁ A₂))
    ext y
    rw [Submodule.mem_comap, mem_mulLat_iff, mem_mulLat_iff, Submodule.mem_comap]
    have h : ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂) * (LinearMap.inl O A₁ A₂ y) =
        LinearMap.inl O A₁ A₂ (((Units.map (MonoidHom.fst A₁ A₂) t)⁻¹ : A₁ˣ) * y) := by
      ext <;> simp
    rw [h]
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).map (LinearMap.snd O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.snd A₁ A₂) t : A₂ˣ) : A₂) ((M : Submodule O (A₁ × A₂)).map (LinearMap.snd O A₁ A₂))
    unfold mulLat
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnitsStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticePair_projection_smul_units : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)), latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  first | exact @GlobalTheory.UnitLemma.latProj_smul | exact GlobalTheory.UnitLemma.latProj_smul | (intros; apply GlobalTheory.UnitLemma.latProj_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedCountStableLatticesProductDescentGL

section

@[expose] public section

open Polynomial

namespace GlobalTheory.UnitLemma.DescentGL

open GlobalTheory.UnitLemma

theorem stab_smul_comm {G X : Type} [CommGroup G] [MulAction G X] (t : G) (x : X) :
    MulAction.stabilizer G (t • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

theorem countGL_prod : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  intro O _ _ _ _ E _ _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ hsep
  have hs₁ := hsep.of_mul_left
  have hs₂ := hsep.of_mul_right
  have hres : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 :=
    resultant_ne_zero _ _ hsep.isCoprime
  rw [GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E (A₁ × A₂) (g₁, g₂), GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₁ g₁, GlobalTheory.T.stableLatticeOrbitCount_eq_sum_orbits O E A₂ g₂]
  haveI hf₁ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₁ g₁ hs₁
  haveI hf₂ := GlobalTheory.T.finite_unit_orbits_stable_lattices_separable O E A₂ g₂ hs₂
  obtain ⟨hfinY, hsum⟩ := GlobalTheory.T.stableLatticePair_orbits_finite_and_card_prod O E A₁ A₂ g₁ g₂ hf₁ hf₂
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField O)).ne'
  have hfib := GlobalTheory.T.ncard_fibre_stableLatticePairProjection O E A₁ A₂ g₁ g₂ hres
  have hstab : ∀ y : LatPair O E g₁ g₂, MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧
      (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) ≠ 0 := by
    intro y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ y (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ y.1) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ y.2)
    exact ⟨h1, by rw [h2]; exact mul_ne_zero (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₁ g₁ hs₁ y.1) (GlobalTheory.T.stabilizer_relIndex_intUnits_ne_zero' O E A₂ g₂ hs₂ y.2)⟩
  have hfin : ∀ y, (latProj O E g₁ g₂ ⁻¹' {y}).Finite := by
    intro y
    apply Set.finite_of_ncard_ne_zero
    have h := hfib y
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zpow_ne_zero _ hq h.symm
  have hCP := GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres (A₁ × A₂)ˣ (stLat O E ((g₁, g₂) : A₁ × A₂)) (LatPair O E g₁ g₂) (intUnits O (A₁ × A₂))
    (latProj O E g₁ g₂) (GlobalTheory.T.stableLatticePair_projection_smul_units O E A₁ A₂ g₁ g₂) hfin hstab hfinY (fun _ => 1) (fun _ _ => rfl)
  simp only [one_mul] at hCP
  rw [hCP]
  have hterm : ∀ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂),
      ((latProj O E g₁ g₂ ⁻¹' {Quotient.out o}).ncard : ℚ) *
        ((MulAction.stabilizer (A₁ × A₂)ˣ (Quotient.out o)).relIndex (intUnits O (A₁ × A₂)) : ℚ) =
      (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) *
        (((MulAction.stabilizer A₁ˣ (Quotient.out o).1).relIndex (intUnits O A₁) : ℚ) *
          ((MulAction.stabilizer A₂ˣ (Quotient.out o).2).relIndex (intUnits O A₂) : ℚ)) := by
    intro o
    rw [hfib, (GlobalTheory.T.stabilizer_stableLatticePair_relIndex_integralUnits O E A₁ A₂ g₁ g₂ _ (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₁ g₁ _) (GlobalTheory.T.stabilizer_stableLattice_le_integralUnitsSubgroup O E A₂ g₂ _)).2, Nat.cast_mul]
  have hs := hsum (fun y => ((MulAction.stabilizer A₁ˣ y).relIndex (intUnits O A₁) : ℚ))
    (fun y => ((MulAction.stabilizer A₂ˣ y).relIndex (intUnits O A₂) : ℚ))
    (fun t y => by simp only [stab_smul_comm]) (fun t y => by simp only [stab_smul_comm])
  rw [finsum_congr hterm, ← mul_finsum, hs]

end GlobalTheory.UnitLemma.DescentGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedCountStableLatticesProductDescentGLStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.weighted_count_stable_lattices_product_descent_GL : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → countGL O E ((g₁, g₂) : A₁ × A₂) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) * (countGL O E g₁ * countGL O E g₂) := by
  first | exact @GlobalTheory.UnitLemma.DescentGL.countGL_prod | exact GlobalTheory.UnitLemma.DescentGL.countGL_prod | (intros; apply GlobalTheory.UnitLemma.DescentGL.countGL_prod <;> assumption)
end
end
