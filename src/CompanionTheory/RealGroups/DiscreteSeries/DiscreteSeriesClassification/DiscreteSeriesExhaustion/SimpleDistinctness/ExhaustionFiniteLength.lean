module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.ExplicitFunctionSquareIntegrable
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfCommute
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open CompanionTheory.RgExh
open Formalism.REAL (IsWeight)
open CompanionTheory.D.LK (LocFin)

variable {n : ℕ}

theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [(X.E a b).map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

theorem pathFin :
    ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n)),
      (LocFin ε X.E → LocFin ε (path X χ ss).E) ∧ (IntWt X → IntWt (path X χ ss)) := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    have h := ih (step X (χ s)) (χ + Pi.single s 1)
    exact ⟨fun hX => h.1 (locFin_step ε X (χ s) hX),
      fun hX => h.2 (intWt_step X (χ s) hX)⟩

end GlobalTheory.CompanionTheory.RgSteps
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber

section

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LowestData

open Formalism.REAL (KHighest)
open _root_.CompanionTheory.RgExh (GMod AlgDS)
open _root_.CompanionTheory.RgDs (InCone)
open GlobalTheory.LowestKTypeDetermines (lt_of_perm_lt rhoC_perm lowK_add strictAnti_add_rho nsq_add_cone eq_zero_of_nsq nsq_comp)

variable {n : ℕ}

theorem kHighest_renumber {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) {s s' : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hs' : ∀ a b, a < b → ε (s' a) = ε (s' b) → s' a < s' b) {Λ : Fin n → ℝ} {v : V}
    (h : KHighest (ε ∘ s') (fun a b => E (s' a) (s' b)) Λ v) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (Λ ∘ s'.symm ∘ s) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h1 (s'.symm (s a))
    simpa using this
  · have hlt := hs a b hab he
    have key : s'.symm (s a) < s'.symm (s b) := by
      refine lt_of_perm_lt (s := s') hs' ?_ ?_
      · simpa only [Equiv.apply_symm_apply] using hlt
      · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he
    have := h2 _ _ key (by simpa using he)
    simpa using this

-- Unfold DataUniq and ConeDS to depend directly on AlgDS and InCone.
theorem dataUniq (n : ℕ) (ε : Fin n → Bool) (X : GMod n)
    (s s' : Equiv.Perm (Fin n)) (mu mu' : Fin n → ℝ)
    (h : AlgDS ε X s mu)
    (hc : ∀ (ν : Fin n → ℝ) (x : X.V), x ≠ 0 →
      KHighest (ε ∘ s) (fun a b => X.E (s a) (s b)) ν x →
      InCone (PI.UpqRep.lowK (ε ∘ s) mu) ν)
    (h' : AlgDS ε X s' mu') : s = s' ∧ mu = mu' := by
  obtain ⟨hl, hs, -, v, hv0, hv⟩ := h
  obtain ⟨hl', hs', hmin', v', hv0', hv'⟩ := h'
  have add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := fun ε lam => lowK_add ε lam
  have k1 := kHighest_renumber ε X.E hs hs' hv'
  have k2 := kHighest_renumber ε X.E hs' hs hv
  obtain ⟨c, hc1, e⟩ := hc _ v' hv0' k1
  have m2 := hmin' _ v hv0 k2
  set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx
  set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ
  have hsx : StrictAnti x := strictAnti_add_rho hl.1
  have hsx' : StrictAnti x' := strictAnti_add_rho hl'.1
  have r1 : x' ∘ s'.symm ∘ s = x + Q := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    have e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := (add _ _).symm
    funext a
    have ea := congrFun e a
    rw [e1, e2, rhoC_perm s hs, rhoC_perm s' hs']
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢
    rw [ea]; ring
  have r2 : x ∘ s.symm ∘ s' =
      PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    rw [e1, rhoC_perm s hs, rhoC_perm s' hs']
    funext a
    simp
  have m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x := by
    have a1 : Formalism.REAL.nsq x' =
        PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu') := by
      rw [hx', ← add]; rfl
    have a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s')
        (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s') := by
      have := nsq_comp (s.symm * s') x
      have e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s' := rfl
      rw [e3, r2] at this
      rw [← this]; rfl
    rw [a1, a2]; exact m2
  have m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x' := by
    rw [← r1]
    exact nsq_comp (s'.symm * s) x'
  have h4 := nsq_add_cone hsx.antitone hc1
  have hQ0 : Q = 0 := eq_zero_of_nsq (by linarith)
  rw [hQ0, add_zero] at r1
  have hm : StrictMono (s'.symm * s) := fun a b hab => by
    have h5 := hsx hab
    rw [← r1] at h5
    exact hsx'.lt_iff_gt.1 h5
  have h6 : s'.symm * s = 1 := by
    have := Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  have h7 : s = s' := by
    refine Equiv.ext fun a => ?_
    have := congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6
    simpa using this
  subst h7
  refine ⟨rfl, ?_⟩
  have h8 : x' = x := by
    simpa using r1
  exact (add_right_cancel h8).symm

end GlobalTheory.CompanionTheory.LowestData
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.KModOfStep

theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    refine ⟨0, ?_, by simp⟩
    funext a
    change χ a = χ a + (↑(0 : ℕ) : ℂ)
    simp
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · change pathEnd (χ + Pi.single s 1) ss = _
      rw [h]
      funext a
      by_cases e : a = s
      · subst a
        simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one]
        ac_rfl
      · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha
      · subst a
        simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_succ (Nat.zero_le (m' s))
      · exact (hm a ha).trans (Nat.le_add_right _ _)

theorem pathEndNat (n : ℕ) (χ : _root_.Fin n → ℂ) (ss : List (_root_.Fin n)) :
    ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a :=
  pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ExhaustionFiniteLength

section

@[expose] public section

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish
    GlobalTheory.CompanionTheory.RgStart.startMod
    GlobalTheory.CompanionTheory.RgSteps.pathFin
    GlobalTheory.CompanionTheory.RgPath.pathExists
    GlobalTheory.CompanionTheory.RgPath.pathEndNat
    GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct
    GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgIso.isoFacts
    GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS
    GlobalTheory.CompanionTheory.LowestDataIso.algUniq
    GlobalTheory.CompanionTheory.LowestData.dataUniq
    GlobalTheory.CompanionTheory.RenumDS.dsOfArr
    GlobalTheory.CompanionTheory.DSData.dsOfData
    GlobalTheory.CompanionTheory.KModOfStep.kModOf
    GlobalTheory.CompanionTheory.ArrCount.arrCount

end CompanionTheory.RgExh.Fin
end
end
