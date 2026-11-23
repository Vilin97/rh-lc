module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecompositionStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseReads

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem exists_base_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (ι : Om l ≃+* ℂ) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g₀ : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ₀.toRingHom.comp c)) = H.emb g₀ → ∃ κ : H.E →+* ↥LL.1, ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ.toRingHom.comp c)) = H.emb g → Reads H c κ τ g := by
  intro R H l _ K LL c ι τ₀ g₀ h₀
  refine ⟨τ₀.toRingHom.comp (c.comp ((H.sigmaOf g₀).symm : H.E →+* H.E)), ?_⟩
  intro τ g hτ x
  have hinj : Function.Injective (fun y : ↥LL.1 => ι (LL.1.val y)) :=
    ι.injective.comp (LL.1.val.injective)
  apply hinj
  have e1 := DFunLike.congr_fun hτ x
  have e2 := DFunLike.congr_fun h₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x))
  simp only [RingHom.comp_apply] at e1 e2
  simp only [RingHom.comp_apply]
  change ι (LL.1.val (τ (c x))) = ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x)))))
  have e1' : ι (LL.1.val (τ (c x))) = H.emb g x := e1
  have e2' : ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x))))) = H.emb g₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x)) := e2
  rw [e1', e2']
  simp [Host.emb]

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CcMulSelf

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem cc_mul_self (φ : Formalism.HC.Frame) : φ.cc * φ.cc = 1 := by
  ext <;> simp [Formalism.HC.Frame.cc, c0]

theorem hcAt_eq_hc : ∀ (D : D7) (ρ : D.what₂.Tau) (g : D.R.GG), (((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨ ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g) → hcAt D g = D.hc ρ := by
  intro D ρ g h
  have hm : ((D.eTau ρ : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2
  have hp : plc g = ((D.eTau ρ : D.R.Psi) : D.R.GG) := by
    rcases h with rfl | rfl
    · simp [plc, hm]
    · unfold plc
      have h2 : (((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc).1.2 ≠ 1 := by
        simp [Formalism.HC.Frame.cc, c0, hm]
      rw [if_neg h2, mul_comm, mul_assoc, cc_mul_self, mul_one]
  unfold hcAt
  have : (⟨plc g, plc_mem g⟩ : D.R.Psi) = D.eTau ρ := Subtype.ext hp
  rw [this, Equiv.symm_apply_apply]

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemTwistedDualJumpsWithoutBlockIff

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem half_int_eq (R : Ranks) : ((((R.t : ℤ) - 1) / 2 : ℤ) : ℚ) = ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨k, hk⟩ := R.t_odd
  rw [hk]
  push_cast
  have : ((2 * (k : ℤ) + 1 - 1) / 2) = k := by omega
  rw [this]; push_cast; ring

theorem mem_cloud_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ cloud P j ↔ ∃ a, (X : ℚ) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold cloud
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.v_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_lows_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (X : ℤ) :
    X ∈ lows P j ↔ ∃ a, (X : ℚ) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2 := by
  obtain ⟨ze, hze⟩ := P.e_int j
  unfold lows
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [← ha, hze, hzv, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rw [half_int_eq]
  · rintro ⟨a, ha⟩
    obtain ⟨zv, hzv⟩ := P.b_int a
    refine ⟨a, ?_⟩
    rw [hze, hzv, Int.floor_intCast, Int.floor_intCast]
    rw [hze, hzv, ← half_int_eq] at ha
    exact_mod_cast ha.symm

theorem mem_twistedDualJumpsWithoutBlock_iff {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    u ∈ jT2 P j s ↔ (if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) ∈ cloud P j + lows P j := by
  unfold jT2 jW
  cases s
  · simp only [Bool.false_eq_true, if_false, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩
  · simp only [if_true, Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1; ring
    · intro h
      exact ⟨_, h, by ring⟩

theorem jumps_rat {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (u : ℤ) :
    (u ∈ jT2 P j s ↔ ((∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j + P.v a + ((R.t : ℚ) - 1) / 2) ∨ ∃ a, (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) = P.e j - P.b a + ((R.t : ℚ) - 1) / 2)) ∧ (u ∈ jT1 P j s ↔ u ∈ jT2 P j s ∨ ∃ c : ℕ, c < R.t ∧ -u - 1 = c) := by
  have hcast : (if s then (-(u : ℚ) - 1) else (R.t : ℚ) - 1 - (-(u : ℚ) - 1)) =
      (((if s then -u - 1 else (R.t : ℤ) - 1 - (-u - 1)) : ℤ) : ℚ) := by
    split_ifs <;> push_cast <;> ring
  refine ⟨?_, ?_⟩
  · rw [mem_twistedDualJumpsWithoutBlock_iff, Multiset.mem_add, hcast, mem_cloud_iff, mem_lows_iff]
  · unfold jT1 jR
    rw [Multiset.map_add (f := _), Multiset.mem_add]
    show u ∈ jT2 P j s ∨ _ ↔ _
    apply or_congr Iff.rfl
    unfold block
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, by ring⟩
    · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by omega⟩

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalJumpSetsEqIntegerMultisetsTwistedDual

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem rat_jump_sets_eq_int_multisets : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  intro D i ρ g ep up hpl hup a
  have hP : hcAt D g = D.hc ρ := hcAt_eq_hc D ρ g hpl
  have hs : pos (if ep then 1 else -1) g = up := by
    unfold LJ.TypeU at hup
    rw [Formalism.HC.Frame.mem_Psi_iff] at hup
    rcases Int.units_eq_one_or g.1.2 with h | h <;> cases ep <;> cases up <;> simp_all [pos]
  have hsz : LJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (liftIdx D i) := by
    have := D.nd.j_range i
    unfold LJ.sz liftIdx
    rw [dite_eq_left (by omega)]
  have hc0 : LJ.c0 D = ((D.R.t : ℚ) - 1) / 2 := rfl
  obtain ⟨h2, h1⟩ := jumps_rat (D.hc ρ) (liftIdx D i) up a
  rw [hP, hs, h1, h2]
  have hblk : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    refine exists_congr fun c => and_congr Iff.rfl ?_
    exact_mod_cast Iff.rfl
  have hblk' : ∀ x : ℤ, (∃ c : ℕ, c < D.R.t ∧ (D.R.t : ℚ) - 1 - (x : ℚ) = (c : ℚ)) ↔ ∃ c : ℕ, c < D.R.t ∧ x = c := by
    intro x
    constructor
    · rintro ⟨c, hc, h⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      have h' : (D.R.t : ℤ) - 1 - x = c := by exact_mod_cast h
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      omega
    · rintro ⟨c, hc, rfl⟩
      refine ⟨D.R.t - 1 - c, by omega, ?_⟩
      push_cast [show c ≤ D.R.t - 1 by omega, show 1 ≤ D.R.t by omega]
      ring
  cases up
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, Bool.false_eq_true, if_false, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk' (-a - 1)
    push_cast at this
    exact this
  · simp only [LJ.dualS, LJ.JJ, LJ.JW, LJ.cloudT, LJ.lowT, LJ.Jm, LJ.Jp, LJ.reflS, LJ.refl, LJ.cloudJ, LJ.lowJ,
      LJ.blockJ, Set.mem_setOf_eq, Set.mem_union, if_true, hsz, hc0]
    refine ⟨or_congr Iff.rfl ?_, by push_cast⟩
    have := hblk (-a - 1)
    push_cast at this
    exact this

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalJumpSetsEqIntegerMultisetsTwistedDualStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) (g : D.R.GG) (ep up : Bool), LJ.PlaceOf D ρ g → (up = true ↔ LJ.TypeU D ep g) → ∀ a : ℤ, ((a : ℚ) ∈ LJ.dualS (LJ.JJ D up (D.nd.j i) ρ) ↔ a ∈ jT1 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) ∧ ((a : ℚ) ∈ LJ.dualS (LJ.JW D up (D.nd.j i) ρ) ↔ a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep then 1 else -1) g)) := by
  first | exact @GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets | exact GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets | (intros; apply GlobalTheory.HTW.Rec.rat_jump_sets_eq_int_multisets <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtension

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec


open Classical in
theorem hodgeTateJumps_coefficientExtension : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  intro D L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  obtain ⟨ep, hep⟩ := hJ
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  have hτ₀ : Nonempty (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥Cx.LL.1) :=
    ⟨((D.nbr i w hw).Kw.1.val).codRestrict Cx.LL.1.toSubalgebra
      (fun x => Cx.le ((D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x))⟩
  obtain ⟨τ₀⟩ := hτ₀
  obtain ⟨g₀, ρ₀, hr₀, -⟩ := hep i r hP.good w hw Cx τ₀
  obtain ⟨κ, hκ⟩ := exists_base_reads D.host (D.nbr i w hw).Kw Cx.LL (Br.cEw D.nbr i w hw)
    (D.naut.iotaQC i) τ₀ g₀ hr₀.1
  refine ⟨if ep then 1 else -1, κ, ?_⟩

  have hc : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), (Continuous fun g => M g) →
      Continuous (TruncatedSeriesCountingIdentities.locC Cx M) := by
    intro k M hM
    refine continuous_matrix fun a b => ?_
    have h1 := locC_cont D i M hM w hw Cx (Pi.single b 1)
    have h2 := (continuous_apply a).comp h1
    simpa [Function.comp_def, Matrix.mulVec_single] using h2
  have hW : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hP.contρ
  refine GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition L C₀ i w hw C r ρ π _ κ hR h7 (hF i w hw Cx).2.2.1
    (fun z => (IntermediateField.inclusion Cx.le).commutes z)
    (fun x => hc _ (rTwO_cont D i r hP.cont x)) (hc _ hW) (fun x => hP.crys w hw Cx x) hP.dec ?_
  intro τ
  obtain ⟨g, ρ', hrd, hx, hπ⟩ := hep i r hP.good w hw Cx τ
  have hup : (decide (LJ.TypeU D ep g) = true ↔ LJ.TypeU D ep g) := decide_eq_true_iff
  have hs := GlobalTheory.T.rationalJumpSets_eq_integerMultisets_twistedDual D i ρ' g ep _ hrd.2 hup
  refine ⟨g, hκ τ g hrd.1, ?_, ?_⟩
  · intro x a ha
    exact ((hs a).1).1 (((hx x a).2.2.1).1 ha)
  · intro a
    refine ((hπ ρ π hP.mem hP.dec a).2.2.2).trans ?_
    by_cases h : a ∈ jT2 (hcAt D g) (liftIdx D i) (pos (if ep = true then 1 else -1) g)
    · rw [if_pos ((hs a).2.2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hs a).2.1 h')), if_neg h]

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtensionStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → ∃ (ε : ℤˣ) (κ : D.host.E →+* ↥Cx.LL.1), JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | exact GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension | (intros; apply GlobalTheory.HTW.Rec.hodgeTateJumps_coefficientExtension <;> assumption)
end
end
