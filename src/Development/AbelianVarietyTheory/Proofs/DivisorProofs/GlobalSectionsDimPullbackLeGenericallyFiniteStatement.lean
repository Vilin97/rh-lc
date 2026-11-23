module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTraceCoefficientsNonvanishingStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackLeMulTwistDominantStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensio

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FunctionFieldCoords

theorem map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem functionFieldMap_finite {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W)
    [IsDominant f] (h : f.residueDegree (genericPoint M) ≠ 0) : (functionFieldMap f).Finite := by
  have hfin : (f.residueFieldMap (genericPoint M)).hom.Finite := by
    letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
    change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
      at h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  have hsurj : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      Function.Surjective (W.presheaf.stalkSpecializes h).hom := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact fun a => ⟨a, rfl⟩
  have hinj : Function.Injective (M.residue (genericPoint M)).hom :=
    RingHom.injective (f := ((M.residue (genericPoint M)).hom : M.functionField →+* _))
  let e := RingEquiv.ofBijective (M.residue (genericPoint M)).hom
    ⟨hinj, M.residue_surjective _⟩
  have key : ∀ (hs : f (genericPoint M) ⤳ genericPoint W),
      ((W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
    intro hs
    have hc : (M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (f.residueFieldMap (genericPoint M)).hom.comp
          ((W.residue _).hom.comp (W.presheaf.stalkSpecializes hs).hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Category.assoc, Category.assoc, Scheme.residue_residueFieldMap]
    have h1 : ((M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
      rw [hc]
      exact hfin.comp (RingHom.Finite.of_surjective _
        ((W.residue_surjective _).comp (hsurj hs (map_genericPoint_eq f))))
    have h2 : (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (e.symm : _ →+* _).comp ((M.residue (genericPoint M)).hom.comp
          (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom) := by
      ext a
      exact (e.symm_apply_apply _).symm
    rw [h2]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp h1
  exact key _

end GlobalTheory.FunctionFieldCoords

theorem GlobalTheory.functionField_coords : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  intro M W _ _ f _ h
  letI := (functionFieldMap f).toAlgebra
  haveI : Module.Finite W.functionField M.functionField :=
    GlobalTheory.FunctionFieldCoords.functionFieldMap_finite f h
  let b := Module.finBasis W.functionField M.functionField
  refine ⟨Module.finrank W.functionField M.functionField, fun j => (b.coord j).toAddMonoidHom,
    fun j c x => ?_, fun x hx => ?_⟩
  · change b.coord j (c • x) = c * b.coord j x
    rw [map_smul, smul_eq_mul]
  · exact b.ext_elem fun i => by simpa using hx i
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensioStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.exists_coordinateFunctionals_functionField_extension : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  first | exact @GlobalTheory.functionField_coords | exact GlobalTheory.functionField_coords | (intros; apply GlobalTheory.functionField_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowAmpleForallLocalCondition

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory

namespace SecLocalCondition

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {W : Scheme.{0}} [IsIntegral W] {H : LB W}

theorem gen_mem_nonzeroLocus_iff {n : ℕ} (s : (lbPow H n).Sec) {J : PUnit → H.ι}
    (hJ : genericPoint W ∈ powChart H J) :
    genericPoint W ∈ nonzeroLocus s ↔ fnOf _ hJ (powFn s J) ≠ 0 := by
  refine (mem_nonzeroLocus_iff_powFn s hJ).trans ((LBGerm.isUnit_gs_iff (𝟙 W) (genericPoint W) (powChart H J) hJ (powFn s J)).trans ?_)
  change genericPoint W ∈ W.basicOpen (powFn s J) ↔ _
  rw [← unitAt_fnOf_iff hJ hJ]
  exact ⟨UnitAt.ne_zero, unitAt_genericPoint⟩

theorem regAt_pow {x : W} {f : W.functionField} (h : RegAt x f) (k : ℕ) : RegAt x (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem exists_local (hA : IsAmpleLB H) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {y : W} {V : W.Opens} (hy : y ∈ V) (d : Γ(W, V))
    (hd : fnOf V (gen_mem hy) d ≠ 0) (hPd : ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) :
    ∃ m, 1 ≤ m ∧ ∃ u : (lbPow H m).Sec, ∃ O : W.Opens, y ∈ O ∧ genericPoint W ∈ nonzeroLocus u ∧
      ∀ y' ∈ O, ∀ (i : (lbPow H m).ι) (hi : y' ∈ (lbPow H m).U i), P y' (fnOf _ (gen_mem hi) (u.f i)) := by
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  obtain ⟨q, hq, s, hys, hle, -⟩ := hA.exists_affine_le hy
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 0) hA.isLB s
    (fun J => resG W (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) d)
    (LBGerm.mem_secOn_of_germ (M := lbPow H 0) _ fun z J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 W) z J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) ⟨hs, hJ⟩ d).trans
        (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J' ≤ V) ⟨hs, hJ'⟩ d).symm)
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  have key : ∀ (J : PUnit → H.ι) (hJ : genericPoint W ∈ powChart H J),
      fnOf _ hJ (powFn u J) = fnOf _ hJ (powFn s J) ^ (N + 1) * fnOf V (gen_mem hy) d := by
    intro J hJ
    have hη : genericPoint W ∈ nonzeroLocus s ⊓ powChart H J := ⟨gen_mem hys, hJ⟩
    have e := congrArg (fnOf _ hη) (hu J)
    rwa [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at e
  refine ⟨0 + q * (N + 1), by nlinarith, u, _, hys, ?_, fun y' hy' i hi => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_chart (isLB_lbPow hA.isLB q) (genericPoint W)
    rw [gen_mem_nonzeroLocus_iff u hJ, key J hJ]
    exact mul_ne_zero (pow_ne_zero _ ((gen_mem_nonzeroLocus_iff s hJ).1 (gen_mem hys))) hd
  · have hr : RegAt y' (fnOf _ (gen_mem hi) (powFn s i) ^ (N + 1)) :=
      regAt_pow (regAt_fnOf hi (gen_mem hi) (powFn s i)) (N + 1)
    have e : fnOf _ (gen_mem hi) (u.f i) = _ := key i (gen_mem hi)
    rw [e]
    exact hP y' _ _ (hPd y' (hle hy')) hr

theorem exists_prod (hL : H.IsLB) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {ι : Type} (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a)
    (u : ∀ a, (lbPow H (m a)).Sec) (hu : ∀ a, genericPoint W ∈ nonzeroLocus (u a)) (Q : ι → W → Prop)
    (hQ : ∀ a y', Q a y' → ∀ (i : (lbPow H (m a)).ι) (hi : y' ∈ (lbPow H (m a)).U i),
      P y' (fnOf _ (gen_mem hi) ((u a).f i))) (T : Finset ι) :
    ∃ n, (T.Nonempty → 1 ≤ n) ∧ ∃ t : (lbPow H n).Sec, genericPoint W ∈ nonzeroLocus t ∧
      ∀ a ∈ T, ∀ y', Q a y' → ∀ (i : (lbPow H n).ι) (hi : y' ∈ (lbPow H n).U i),
        P y' (fnOf _ (gen_mem hi) (t.f i)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, fun h => absurd h Finset.not_nonempty_empty, secOfFn H 1, ?_, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    rw [nonzeroLocus_secOfFn hL, Scheme.basicOpen_one]
    trivial
  | insert b T hb ih =>
    obtain ⟨n, -, t, ht, htP⟩ := ih
    refine ⟨m b + n, fun _ => le_add_right (hm b), secMul (u b) t,
      (nonzeroLocus_secMul (u b) t).ge ⟨hu b, ht⟩, fun a ha y' hy' i hi => ?_⟩
    have e : fnOf _ (gen_mem hi) ((secMul (u b) t).f i) =
        fnOf _ (gen_mem hi) ((u b).f i) * fnOf _ (gen_mem hi) (t.f i) :=
      map_mul (fnOf _ (gen_mem hi)) ((u b).f i) (t.f i)
    rw [e]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · rw [mul_comm]
      exact hP y' _ _ (hQ a y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)
    · exact hP y' _ _ (htP a ha y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)

end SecLocalCondition


open SecLocalCondition in
theorem exists_sec_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H →
    ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) →
    (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) →
    ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧
      ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  intro W _ H hA P hP hloc
  have := hA.compactSpace
  choose V hy d hd hPd using hloc
  choose m hm u O hyO hu hQ using fun y => exists_local hA P hP (hy y) (d y) (hd y) (hPd y)
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top O hyO
  obtain ⟨n, hn, t, ht, htP⟩ := exists_prod hA.isLB P hP m hm u hu (fun a y' => y' ∈ O a) hQ T
  refine ⟨n, hn ?_, t, (sec_ne_zero_iff t).2 ht, fun y i hi => ?_⟩
  · obtain ⟨a, -⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (genericPoint W)))
    exact ⟨a, a.2⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ y))
    exact htP a a.2 y ha i hi

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowAmpleForallLocalConditionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier


theorem _root_.GlobalTheory.T.exists_section_pow_ample_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H → ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) → (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧ ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) → ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧ ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  first | exact @GlobalTheory.exists_sec_forall_local_condition | exact GlobalTheory.exists_sec_forall_local_condition | (intros; apply GlobalTheory.exists_sec_forall_local_condition <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFinite

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GlobalSectionsPullback

theorem globalSectionsDim_pullback_le_generically_finite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f →
    f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧
      ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤
        r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f hp hfp _ hdeg
  obtain ⟨r, co, hco, hinj⟩ := GlobalTheory.T.exists_coordinateFunctionals_functionField_extension M W f hdeg
  obtain ⟨hpp, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hfpp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (f ≫ p)).1 hfp
  haveI := hpp
  haveI := hfpp
  haveI : IsProper f := IsProper.of_comp f p
  haveI : IsNoetherian W := isNoetherian_of_isProjOver hp
  obtain ⟨n, hn, t, ht, htP⟩ := GlobalTheory.T.exists_section_pow_ample_forall_local_condition W H hH
    (fun y c => ∀ (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (c * co j (fnOf (f ⁻¹ᵁ V') h z)))
    (fun y c c' hc hc' V' hy h z j => by rw [mul_assoc]; exact hc'.mul (hc V' hy h z j))
    (fun y => by
      obtain ⟨V, hy, d, hd, hd'⟩ := GlobalTheory.T.exists_open_trace_coefficients_nonvanishing M W f L hL co hco y
      exact ⟨V, hy, d, hd, fun y' hy' V' hV' h z j => hd' y' hy' V' hV' h z j⟩)
  exact ⟨r, lbPow H n, (isAmpleLB_pow_iff hH.isLB hn).2 hH, fun B hB =>
    GlobalTheory.T.finrank_sections_pullback_le_mul_twist_of_dominant F M W p f hp co hco hinj (lbPow H n) (isLB_lbPow hH.isLB n) t ht
      (fun y i hi V' hV' h z j => htP y i hi V' hV' h z j) B hB⟩

end GlobalTheory.GlobalSectionsPullback
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFiniteStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.exists_ample_sections_pullback_bound_of_genFinite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f → f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧ ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  first | exact @GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite | exact GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite | (intros; apply GlobalTheory.GlobalSectionsPullback.globalSectionsDim_pullback_le_generically_finite <;> assumption)
end
end
