module

public import GroundTheory.ProfiniteCohomology.PoitouTate.Deduction
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsLocalInvRootsOfPlaces
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.ZmodToQZGsCompactInvLocalToCompactEqLocalInvU
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
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
import Mathlib.Tactic.TypeStar
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BasePairing

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

omit [Fintype S] [NeZero n] in
theorem zmodCocycleHom_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    zmodCocycleHom z 1 = 0 := by
  have h := zmodCocycleHom_mul z 1 1
  rw [mul_one] at h
  exact (add_eq_left.1 h.symm)


omit [Fintype S] in
def gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)) where
  toFun g := Multiplicative.ofAdd (zmodCocycleHom z g)
  map_one' := by rw [zmodCocycleHom_one]; rfl
  map_mul' g h := by rw [zmodCocycleHom_mul]; rfl
  continuous_toFun := ((isLocallyConstant_zmodCocycleHom z).comp Multiplicative.ofAdd).continuous

omit [Fintype S] [NeZero n] in
theorem toAdd_gsCharOfCocycle (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (g : galUnramifiedOutside K.1 ℚ̄ S) : Multiplicative.toAdd (gsCharOfCocycle S n z g) = zmodCocycleHom z g :=
  rfl


omit [Fintype S] [NeZero n] in
theorem eq_zero_of_gsCharOfCocycle_eq_one (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hz : gsCharOfCocycle S n z = 1) : z = 0 := by
  apply cocycles_ext
  funext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  have e : zmodCocycleHom z (v 0) = 0 := congrArg Multiplicative.toAdd (DFunLike.congr_fun hz (v 0))
  rw [hv]
  apply ULift.ext
  exact e.trans (congrArg (fun w => (cochainOf (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) w ![v 0]).down)
    (map_zero (cocycleι (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1))).symm


omit [Fintype S] [NeZero n] in
theorem exists_gsCharOfCocycle_eq
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) :
    ∃ z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (gsCharOfCocycle S n z : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) = χ := by
  have hf : IsLocallyConstant fun g => (ULift.up (Multiplicative.toAdd (χ g)) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) :=
    ((IsLocallyConstant.iff_continuous (fun g : galUnramifiedOutside K.1 ℚ̄ S => χ g)).2 χ.continuous).comp
      fun x : Multiplicative (ZMod n) => (ULift.up (Multiplicative.toAdd x) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
  have hmul : ∀ g h : galUnramifiedOutside K.1 ℚ̄ S,
      (ULift.up (Multiplicative.toAdd (χ (g * h))) : zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) =
        ULift.up (Multiplicative.toAdd (χ g)) + ULift.up (Multiplicative.toAdd (χ h)) := fun g h => by
    apply ULift.ext
    change Multiplicative.toAdd (χ (g * h)) = Multiplicative.toAdd (χ g) + Multiplicative.toAdd (χ h)
    rw [map_mul, toAdd_mul]
  refine ⟨cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (fun _ _ => rfl) _ hf hmul, ?_⟩
  ext g
  apply Multiplicative.toAdd.injective
  rw [toAdd_gsCharOfCocycle]
  exact congrArg ULift.down (cochainOf_cocyclesOneOfHom (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (fun _ _ => rfl) _ hf hmul ![g])

variable (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

omit [Fintype S] [NeZero n] in
include hnk hS in
theorem hnS_of_hS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv => by
  subst hnk
  exact pow_notMem_asIdeal_of_forall S ℓ k hS v hv


include hℓ hnk hS in
theorem gsCompactInv_gsCupClass (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (d : GsUnitsDatum S)
    (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) =
      Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z)
        (Additive.toMul (gsUnitsClass S d))) :=
  zmodToQZ_injective (n := n) (zmodToQZ_gsCompactInv_gsCupClass S ιs n hnS ℓ k hℓ hnk hS hodd h3 d z
    (gsCharOfCocycle S n z) (fun _ => rfl))


omit [Fintype S] [NeZero n] in
theorem eq_zero_of_coprime_nsmul_zmod (hnk : n = ℓ ^ k) {m : ℕ} (hm : m.Coprime ℓ) {u : ZMod n}
    (h : m • u = 0) : u = 0 := by
  have hmn : m.Coprime n := hnk ▸ hm.pow_right k
  rw [nsmul_eq_mul] at h
  exact (ZMod.unitOfCoprime m hmn).isUnit.mul_right_eq_zero.1 h



include hℓ hnk hS in
theorem gsCompactInv_ker_left (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (hx : ∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    x = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  have hz := cohomologyπ_surjective (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1 x
  by_contra hne
  have hχ : gsCharOfCocycle S n hz.choose ≠ 1 := fun h => hne (hz.choose_spec.symm.trans
    ((congrArg (cohomologyπ _ 1) (eq_zero_of_gsCharOfCocycle_eq_one S n _ h)).trans (map_zero _)))
  have hψ : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) ≠ 1 :=
    fun h => hχ ((MulEquiv.map_eq_one_iff _).1 h)
  have ha : ∃ a, charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) a ≠ 1 :=
    not_forall.1 fun h => hψ (MonoidHom.ext h)
  have hm := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS (Additive.ofMul ha.choose)
  have hd := hm.choose_spec.2
  have h1 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS hd.choose hz.choose) = 0 :=
    (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
      (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
      ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
        (gsUnitsData S ιs hd.choose))) w)) hz.choose_spec).trans (hx _)
  have h2 := (gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS hd.choose hz.choose).symm.trans h1
  have h4 : Additive.toMul (gsUnitsClass S hd.choose) = ha.choose ^ hm.choose :=
    (congrArg Additive.toMul hd.choose_spec).trans (toMul_nsmul _ _)
  have h5 : hm.choose • Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose)
      ha.choose) = 0 :=
    (toAdd_pow _ _).symm.trans ((congrArg Multiplicative.toAdd (map_pow _ _ _)).symm.trans
      ((congrArg (fun u => Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n hz.choose) u))
        h4).symm.trans h2))
  exact ha.choose_spec (Multiplicative.toAdd.injective
    (eq_zero_of_coprime_nsmul_zmod n ℓ k hnk hm.choose_spec.1 h5))

theorem exists_nsmul_eq_of_forall_zmod {A : Type*} [AddCommGroup A] (a : A)
    (h : ∀ f : A →+ ZMod n, f a = 0) : ∃ b, n • b = a := by
  by_contra hne
  set N := (nsmulAddMonoidHom (α := A) n).range
  have hq : (QuotientAddGroup.mk' N a) ≠ 0 := fun h0 =>
    hne ((QuotientAddGroup.eq_zero_iff a).1 h0 |>.elim fun b hb => ⟨b, hb⟩)
  have htors : ∀ q : A ⧸ N, n • q = 0 := fun q =>
    QuotientAddGroup.induction_on q fun x => by
      rw [← QuotientAddGroup.mk_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩
  obtain ⟨f, hf⟩ := zmod_exists_apply_ne_zero htors hq
  exact hf (h (f.comp (QuotientAddGroup.mk' N)))



include hℓ hnk hS in
theorem gsCompactInv_ker_right (y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2)
    (hy : ∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) :
    y = 0 := by
  have hnS := hnS_of_hS S n ℓ k hnk hS
  by_cases hk : k = 0
  · have hn1 : n = 1 := by rw [hnk, hk, pow_zero]
    have e := nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) 2 y
    subst hn1
    exact (one_smul _ _).symm.trans e
  have hoddℓ : Odd ℓ ∨ IsTotallyComplex K.1 :=
    hodd.imp (fun h => Nat.not_even_iff_odd.1 fun he => Nat.not_even_iff_odd.2 (hnk ▸ h) (Nat.even_pow.2 ⟨he, hk⟩)) id
  obtain ⟨h, hh⟩ := surjective_gsKummerCompactδ S ιs n hnS ℓ k hℓ hnk hS hoddℓ ((gsRootsComparison S ιs n 2).hom y)
  obtain ⟨d, hd⟩ := gsUnitsData_surjective S ιs h
  have hyeq : y = (gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom
      (gsUnitsData S ιs d)) :=
    (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
      (congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom
        (hh.symm.trans (congrArg (gsKummerCompactδ S ιs n hnS 1).hom hd.symm)))

  have hall : ∀ f : Additive (SIdeleClassGroup S) →+ ZMod n, f (gsUnitsClass S d) = 0 := by
    intro f
    obtain ⟨z, hz⟩ := exists_gsCharOfCocycle_eq S n
      ((charEquiv ℚ̄ (Set.toFinite S) hodd).symm (AddMonoidHom.toMultiplicative f))
    have e1 := gsCompactInv_gsCupClass S ιs n ℓ k hℓ hnk hS hodd h3 hnS d z
    have e2 : gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z) = 0 :=
      (congrArg (fun w => gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs)
        (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) w
        (cohomologyπ _ 1 z))) hyeq).symm.trans (hy _)
    have e3 : charEquiv ℚ̄ (Set.toFinite S) hodd (gsCharOfCocycle S n z) = AddMonoidHom.toMultiplicative f :=
      (congrArg (charEquiv ℚ̄ (Set.toFinite S) hodd) hz).trans (MulEquiv.apply_symm_apply _ _)
    exact (congrArg (fun ψ => Multiplicative.toAdd (ψ (Additive.toMul (gsUnitsClass S d)))) e3).symm.trans
      (e1.symm.trans e2)
  obtain ⟨b, hb⟩ := exists_nsmul_eq_of_forall_zmod n (A := Additive (SIdeleClassGroup S)) _ hall
  obtain ⟨m, hm, d', hd'⟩ := exists_coprime_gsUnitsClass_eq S ℓ hℓ hS b
  have hc0 : gsUnitsClass S (m • d - n • d') = 0 := by
    rw [map_sub, map_nsmul, map_nsmul, ← hb, hd']
    exact sub_eq_zero_of_eq ((smul_smul m n b).trans ((congrArg (· • b) (mul_comm m n)).trans (smul_smul n m b).symm))
  have hd0 := gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero S ιs _ hc0
  rw [map_sub, map_nsmul, map_nsmul, sub_eq_zero, hd] at hd0
  have hw1 : m • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hh, ← map_nsmul, hd0, map_nsmul, nsmul_gsRootsCompact S ιs n hnS]
  have hw2 : ℓ ^ k • (gsRootsComparison S ιs n 2).hom y = 0 := by
    rw [← hnk]
    exact nsmul_gsRootsCompact S ιs n hnS 2 _
  have hw := eq_zero_of_coprime_nsmul_eq_zero hm hw1 hw2
  exact (hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).hom_inv_id y).symm.trans
    ((congrArg (gsRootsComparisonIso S ιs n hnS 2).inv.hom hw).trans (map_zero _))

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseMain

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))


include hℓ hnk hS in
theorem gsBaseBijective_of_fixing (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) :
    GsBaseBijective S ιs n U (gsCompactInv S ιs n hodd h3) := by
  obtain ⟨L, hKL, hL, hUeq⟩ := exists_gsOpenSubgroup_eq K S U
  subst U
  -- Infer the application type before comparing it with the goal.
  have hbase := @gsBaseBijective_of_le K S ‹Fintype S› ιs n ℓ k ‹NeZero n›
    hℓ hnk hS hodd h3 hP hcores W₀ hW₀ L hKL hL hU
  assumption



include hℓ hnk hS in
theorem exists_compactDualityHypotheses_gs_of_pairing (hP : GsPairingInput n ℓ) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have hSn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    mem_of_natCast_pow_mem S n ℓ k hnk hS
  have hD := nonempty_addEquiv_gsRoots_of_places S n hnS
  have hfin : Finite (gsRoots S n) := hD.elim fun e => Finite.of_equiv (ZMod n) e.toEquiv.symm
  have hn : n ≠ 0 := NeZero.ne n
  have hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom := fun U =>
    @surjective_gs_compactCores_three K S ιs n hn hSn hodd U (gsRoots S n)
      (isDiscreteRep_gsRoots S n) hfin (nsmul_gsRoots S n)
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S n hn
  refine ⟨W₀, { nonempty_addEquiv := hD, subsingleton_four := ?_, bijective_base := ?_ }⟩
  · intro M hdiscrete _ hM
    exact @subsingleton_compactCohomology_four K S n hn hSn hodd ιs M hdiscrete hM
  · intro U hU
    have hbase := @gsBaseBijective_of_fixing K S ‹Fintype S› ιs n ℓ k ‹NeZero n›
      hℓ hnk hS hodd h3 hP hcores W₀ hW₀ U hU
    -- The field uses the same map with a different proof of the torsion condition.
    unfold GsBaseBijective at hbase
    with_reducible assumption


include hℓ hnk in
theorem gsPairingInput : GsPairingInput n ℓ := fun _ S' _ ιs' hS' _ hodd' h3' =>
  ⟨gsCompactInv_ker_left S' ιs' n ℓ k hℓ hnk hS' hodd' h3', gsCompactInv_ker_right S' ιs' n ℓ k hℓ hnk hS' hodd' h3'⟩


include hℓ hnk hS in
theorem exists_compactDualityHypotheses_gs :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ :=
  exists_compactDualityHypotheses_gs_of_pairing S ιs n ℓ k hℓ hnk hS hodd h3 (gsPairingInput n ℓ k hℓ hnk)

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)


omit [NeZero N] in
theorem gsBaseCase : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀ :=
  fun p hp => exists_compactDualityHypotheses_gs S ιs _ p _ (Nat.prime_of_mem_primeFactors hp) rfl
    (mem_of_natCast_dvd_mem S hS (Nat.dvd_of_mem_primeFactors hp)) _ _

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)


include hM in
theorem poitouTate_duality_gs {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap (gsFinFamily S ιs) (gsRoots S N) h (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_compactDualityMap M hM h


include hM in
theorem poitouTate_sha_gs :
    Finite (ptSha (gsFinFamily S ιs) M 1) ∧ Finite (ptSha (gsFinFamily S ιs) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))).flip :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).sha M hM


include hM in
theorem poitouTate_nineTerm_gs :
    Function.Injective (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).nineTerm M hM

end GroundTheory.ProfCoh
end
end
end
