module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIntegralFixedVectorsEqOneAlmostAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProdStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnOfNotFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeOperatorSplitOnePlace

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.Peel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem globFn_eq (hU : Unr E) {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) {w : Pl E} (hw : w ∈ S) (x : finU (E := E) (n := n)) :
    globFn S f x = f w (toSub _ (cLoc w x.1)) * ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1)) := by
  have hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u hu ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  conv_lhs => rw [← Set.insert_diff_self_of_mem hw]
  exact finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)

theorem trOn_hop_peel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  intro E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ
  obtain ⟨e, he⟩ := LocCompU.exists_equiv hU n w
  let ι : UL n w →* finU (E := E) (n := n) := (Subgroup.inclusion (inf_le_left : locU n w ≤ finU (E := E) (n := n))).comp
    e.toMulEquiv.symm.toMonoidHom
  let r : finU (E := E) (n := n) →* UL n w := ((cLoc w).comp (finU (E := E) (n := n)).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1
  have hιw : ∀ h, cLoc w (ι h).1 = h.1 := fun h => by
    change cLoc w ((e.symm h : locU n w) : UA E n) = _
    rw [← he, e.apply_symm_apply]
  have hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1 := fun h u hu huw => by
    obtain ⟨v, -, hv⟩ := hS w
    exact GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)
  have hr : ∀ h, r (ι h) = h := fun h => Subtype.ext (hιw h)
  have hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h) := fun x hx h => by
    have h1 : cLoc w x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1 := by
      apply e.injective
      rw [map_one]
      refine Subtype.ext ((he _).trans ?_)
      exact (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1
    have h3 := GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)
    rw [h2, OneMemClass.coe_one, inv_one, one_mul] at h3
    exact Subtype.ext h3.eq
  have hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K' := fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by
    by_cases huw : u = w
    · subst huw
      have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k := Subtype.ext (hιw k)
      rwa [this]
    · have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1 := Subtype.ext (hιu k u hu huw)
      rw [this]
      exact one_mem _
  have hK2 : ∀ k ∈ globLev S K', r k ∈ K' w := fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw
  obtain ⟨hind, h0, -⟩ := GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ
  set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'
  have hf' : IsTest (KL n) K' (Function.update f w a') := by
    refine ⟨fun u => ?_, ?_⟩
    · by_cases huw : u = w
      · subst huw
        rwa [Function.update_self]
      · rw [Function.update_of_ne huw]
        exact hf.1 u
    · filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2
      rwa [Function.update_of_ne h2]
  let b : r.ker → ℂ := fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))
  have hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) →
      ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x := fun g hg hgf h x => by
    rw [globFn_eq hU hg.2 hw]
    have h1 : cLoc w x.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
    congr 1
    · rw [Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dite_eq_left h.2]
    · refine finprod_mem_congr rfl fun u hu => ?_
      rw [hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]
  have hF := hsplit f hf fun _ _ => rfl
  have hF' := hsplit _ hf' fun u hu => Function.update_of_ne hu _ _
  simp only [Function.update_self] at hF'
  have hH := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hH' := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'
  have hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x := fun x => by
    have := hF' 1 x
    rw [map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul] at this
    exact this.symm
  have hopen := (GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1
  have hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K'))
      ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU (E := E) (n := n))
      change globFn S _ _ ≠ 0
      rw [hk, (hH'.2 _ k.2 _).2, ← hb]
      exact hq
    · have h' : ((((p.out : r.ker) : finU (E := E) (n := n))) : finU (E := E) (n := n) ⧸ globLev S K') = ((q.out : r.ker) : finU (E := E) (n := n)) := h
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := QuotientGroup.eq.1 h'
      simpa using this
  haveI := σ.irred
  have hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι) := by
    obtain ⟨p, hp, -, φ, hφ0, hφm, hφ⟩ := hσ
    have hpe : ∀ g, p (e.symm g) = g := fun g => Subtype.ext ((hp _).trans (hιw g))
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let s : UL n w →* UA E n := (finU (E := E) (n := n)).subtype.comp ι
    let Φ : σ.ρ.IntertwiningMap (π'.rep.comp s) :=
      ⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by
        have := hφ (e.symm g) v
        rw [hpe] at this
        exact this)⟩
    have hΦ0 : Φ ≠ 0 := fun h =>
      hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨h1, -⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep
      σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by
        have h3 := GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)
        have h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g := by
          change ((e.symm (e _) : locU n w) : UA E n) = _
          rw [e.symm_apply_apply]
        rw [h4]
        exact h3⟩) Φ hΦ0
    intro v hv
    have hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤
        (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype := by
      refine iSup_le fun ψ => ?_
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y =>
        congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ :
          σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩
    rw [h1] at hle
    exact hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)
  exact trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _
    (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2
    (fun k hk x => by
      rw [hb, hb, hb]
      exact hH'.2 _ hk _)
    (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin

end GlobalTheory.BCT.Peel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeOperatorSplitOnePlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_heckeOperator_split_one_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  first | exact @GlobalTheory.BCT.Peel.trOn_hop_peel | exact GlobalTheory.BCT.Peel.trOn_hop_peel | (intros; apply GlobalTheory.BCT.Peel.trOn_hop_peel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndexStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'), hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  first | exact @GlobalTheory.BCT.hop_indicator_level | exact GlobalTheory.BCT.hop_indicator_level | (intros; apply GlobalTheory.BCT.hop_indicator_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTraces

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_eq_zero_of_finrank_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (h : Module.finrank ℂ M = 0) : trOn M L = 0 := by
  unfold trOn
  split_ifs with hL
  · by_cases hf : FiniteDimensional ℂ M
    · haveI := hf
      haveI : Subsingleton M := Module.finrank_zero_iff.mp h
      rw [Subsingleton.elim (L.restrict hL) 0, map_zero]
    · rw [LinearMap.trace, dite_eq_right]
      · rfl
      · rintro ⟨s, ⟨b⟩⟩
        exact hf (Module.Finite.of_basis b)
  · rfl

theorem trOn_of_eq_smul {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (L : V →ₗ[ℂ] V) (c : ℂ) (h : ∀ v ∈ M, L v = c • v) : trOn M L = c * Module.finrank ℂ M := by
  have hM : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [h v hv]; exact M.smul_mem c hv
  unfold trOn
  rw [dite_eq_left hM]
  have hr : L.restrict hM = c • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, h v v.2]
  rw [hr, map_smul, smul_eq_mul]
  by_cases hf : FiniteDimensional ℂ M
  · rw [LinearMap.trace_id]
  · rw [LinearMap.trace, dite_eq_right, Module.finrank_of_not_finite hf]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hf (Module.Finite.of_basis b)

theorem trOn_hop_eq_dimW_mul_finprod_twTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  intro E _ _ _ hU n hn π hπ S hS lam hlam K' hK' σ hσ f hf
  have hTW := fun w => GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (K' w) (hK'.1 w) (σ w)
  have hcongr : ∀ g g' : ∀ w : Pl E, UL n w → ℂ, (∀ w ∈ S, g w = g' w) → hop S K' g = hop S K' g' := by
    intro g g' h
    have : globFn S g = globFn S g' := by
      funext x
      unfold globFn
      exact finprod_mem_congr rfl (fun w hw => by rw [h w hw])
    unfold hop
    rw [this]
  have hfin : {w | ¬ ((f w = ((KL n w : Set (UL n w)).indicator 1) ∧ K' w = KL n w) ∧
      Module.finrank ℂ (fixed (σ w).ρ (KL n w)) = 1)}.Finite :=
    Filter.eventually_cofinite.1 ((hf.2.and hK'.2).and (GlobalTheory.T.finrank_integral_fixed_vectors_eq_one_almost_all E hU n hn π hπ σ hσ))
  set F := hfin.toFinset with hF
  have hout : ∀ w, w ∉ F → f w = (K' w : Set (UL n w)).indicator 1 ∧
      twTr (σ w).ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = 1 ∧
      (K' w).relIndex (KL n w) = 1 ∧ Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by
    intro w hw
    rw [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    have hr : (K' w).relIndex (KL n w) = 1 := by rw [h2]; exact Subgroup.relIndex_self _
    have hd : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 1 := by rw [h2]; exact h3
    refine ⟨by rw [h1, h2], ?_, hr, hd⟩
    rw [(hTW w).2.2.1, hr, hd]
    simp
  set one : ∀ w : Pl E, UL n w → ℂ := fun w => (K' w : Set (UL n w)).indicator 1 with hone
  have key : ∀ U : Finset (Pl E), (↑U : Set (Pl E)) ⊆ S →
      trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
        ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) *
        trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one, one_mul]
    | insert a U ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a U)
      have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hg : IsTest (KL n) K' (fun w => if w ∈ insert a U then f w else one w) := by
        refine ⟨fun w => ?_, ?_⟩
        · by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact hf.1 w
          · simp only [h, if_false]; exact (hTW w).1
        · filter_upwards [hf.2, hK'.2] with w h1 h2
          by_cases h : w ∈ insert a U
          · simp only [h, if_true]; exact h1
          · simp only [h, if_false, hone]; rw [h2]
      have hstep := GlobalTheory.T.trace_heckeOperator_split_one_place E hU n hn π hπ S hS K' hK' _ hg a haS (σ a) (hσ a)
      have hupd : Function.update (fun w => if w ∈ insert a U then f w else one w) a
          ((K' a : Set (UL n a)).indicator 1) = fun w => if w ∈ U then f w else one w := by
        funext w
        by_cases h : w = a
        · subst h
          simp [ha, hone]
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd] at hstep
      simp only [Finset.mem_insert_self, if_true] at hstep
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have e1 : twTr (σ a).ρ (KL n a) (K' a) (one a) LinearMap.id =
          twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id := rfl
      rw [e1]
      calc _ = (trOn (π ⊓ fixed (RF E n) (globLev S K'))
              (hop S K' (fun w => if w ∈ insert a U then f w else one w)) *
            twTr (σ a).ρ (KL n a) (K' a) ((K' a : Set (UL n a)).indicator 1) LinearMap.id) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id := by ring
        _ = twTr (σ a).ρ (KL n a) (K' a) (f a) LinearMap.id *
            (trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (fun w => if w ∈ U then f w else one w)) *
            ∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id) := by rw [hstep]; ring
        _ = _ := by rw [ih hUS]; ring
  set U := F.filter (· ∈ S) with hUdef
  have hUS : (↑U : Set (Pl E)) ⊆ S := fun x hx => (Finset.mem_filter.1 hx).2
  have hfU : hop S K' (fun w => if w ∈ U then f w else one w) = hop S K' f := by
    refine hcongr _ _ fun w hw => ?_
    by_cases h : w ∈ F
    · have : w ∈ U := Finset.mem_filter.2 ⟨h, hw⟩
      simp only [this, if_true]
    · have : w ∉ U := fun h' => h (Finset.mem_filter.1 h').1
      simp only [this, if_false, hone]
      exact ((hout w h).1).symm
  have hkey := key U hUS
  rw [hfU] at hkey

  have hfp : ∀ g : Pl E → ℂ, (∀ w, w ∉ F → g w = 1) → ∏ᶠ w ∈ S, g w = ∏ w ∈ U, g w := by
    intro g hg
    refine finprod_mem_eq_prod_of_subset g ?_ (fun x hx => (Finset.mem_filter.1 hx).2)
    rintro w ⟨hwS, hw1⟩
    by_cases h : w ∈ F
    · exact Finset.mem_filter.2 ⟨h, hwS⟩
    · exact absurd (hg w h) hw1
  have hRf := hfp (fun w => (((K' w).relIndex (KL n w) : ℕ) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.1])
  have hDf := hfp (fun w => (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) (fun w hw => by simp [(hout w hw).2.2.2])
  have hTf := hfp (fun w => twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) (fun w hw => by
    rw [(hout w hw).1]; exact (hout w hw).2.1)
  have hbase : trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' one) =
      (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) :=
    trOn_of_eq_smul _ _ _ fun φ hφ => GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index E hU n hn S hS K' hK' φ (Submodule.mem_inf.1 hφ).2
  have hdim := GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod E hU n hn π hπ S hS lam hlam K' hK' σ hσ
  have hone_w : ∀ w, twTr (σ w).ρ (KL n w) (K' w) (one w) LinearMap.id =
      ((((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ * (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) :=
    fun w => (hTW w).2.2.1
  rw [Finset.prod_congr rfl (fun w _ => hone_w w)] at hkey
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hkey
  rw [hbase, hdim, hRf, hDf] at hkey
  rw [hTf]
  have hR : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => Nat.cast_ne_zero.2 (hTW w).2.1
  by_cases hD : (∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ)) = 0
  · obtain ⟨w, hwU, hw0⟩ := Finset.prod_eq_zero_iff.1 hD
    have hw0' : Module.finrank ℂ (fixed (σ w).ρ (K' w)) = 0 := by exact_mod_cast hw0
    have hT0 : (∏ w ∈ U, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id) = 0 :=
      Finset.prod_eq_zero hwU ((hTW w).2.2.2 hw0' (f w))
    rw [hT0, mul_zero]
    apply trOn_eq_zero_of_finrank_eq_zero
    have : (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = 0 := by
      rw [hdim, hDf, hD, mul_zero]
    exact_mod_cast this
  · have hne : (∏ w ∈ U, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ *
        ∏ w ∈ U, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hR) hD
    apply mul_right_cancel₀ hne
    rw [hkey]
    ring

end GlobalTheory.BCT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceHeckeLevelVectorsEqDimMulLocalTracesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_hecke_levelVectors_eq_dim_mul_local_traces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * ∏ᶠ w ∈ S, twTr (σ w).ρ (KL n w) (K' w) (f w) LinearMap.id := by
  first | exact @GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | exact GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr | (intros; apply GlobalTheory.BCT.trOn_hop_eq_dimW_mul_finprod_twTr <;> assumption)
end
end
