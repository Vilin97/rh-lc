module

public import Formalism.PeriodIntegrals.LevelKSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.HeisenbergParabolicAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfHL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviInfUnipotentEqOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousLevLMat

section

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}



theorem continuous_uT (P : Frame E M r) (a b : Fin r) :
    Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := by
  have h1 : Continuous fun g : HA (Af F) σ J => lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b)) :=
    PI.LevelKSplit.W.ExC.continuous_lin _
  have h0 : Continuous fun g : HA (Af F) σ J =>
      ((ratV (F := F) (Af F) (P.f a), lin (Af F) σ J g (ratV (F := F) (Af F) (P.e b))) :
        (Fin M → Af F ⊗[F] E) × (Fin M → Af F ⊗[F] E)) :=
    continuous_const.prodMk h1
  have h3 := PI.VolStabSW.continuous_hR (R := Af F) σ J
  have h2 := h3.comp h0
  unfold uT
  simp only [Matrix.of_apply]
  split_ifs
  · exact h2
  · exact continuous_const
  · exact continuous_const

theorem continuous_levL_mat (T : F) (P : Frame E M r) {X : Type} [TopologicalSpace X]
    {U W : X → Matrix (Fin r) (Fin r) (Af F ⊗[F] E)}
    (hU : ∀ a b, Continuous fun x => U x a b) (hW : ∀ a b, Continuous fun x => W x a b) :
    Continuous fun x => LinearMap.toMatrix' (levL (datR (Af F) σ J P T) (U x) (W x)) := by

  simp only [levL, map_add (f := _), map_sum, map_smul]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (hU a b).smul continuous_const)).add
    (continuous_finsetSum _ fun d _ => continuous_finsetSum _ fun b _ => (hW d b).smul continuous_const)

theorem continuous_levG (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : Continuous (levG (R := Af F) hσσ hJ hP) := by
  have hU : ∀ a b, Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g a b := continuous_uT P
  have hUm : Continuous fun g : HA (Af F) σ J => uT (Af F) σ J P g :=
    continuous_pi fun a => continuous_pi fun b => hU a b
  have hIm : Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g := by
    unfold uI
    exact hUm.matrix_adjugate
  have hI : ∀ a b, Continuous fun g : HA (Af F) σ J => uI (Af F) σ J P g a b := fun a b =>
    (continuous_apply b).comp ((continuous_apply a).comp hIm)
  have hcI : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uI (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hI b a)
  have hcT : ∀ a b, Continuous fun g : HA (Af F) σ J => cj (Af F) σ (uT (Af F) σ J P g) a b := by
    intro a b
    unfold cj
    simp only [Matrix.of_apply]
    exact (PI.AdicCompletionValuation.continuous_sigR (R := Af F) σ).comp (hU b a)
  have hM : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)) := by
    simp only [lin_levG]
    exact continuous_levL_mat T P hU hcI
  have hMi : Continuous fun g : HA (Af F) σ J =>
      LinearMap.toMatrix' (lin (Af F) σ J (levG hσσ hJ hP g)⁻¹) := by
    have e : ∀ g : HA (Af F) σ J, lin (Af F) σ J (levG hσσ hJ hP g)⁻¹ =
        levL (datR (Af F) σ J P T) (uI (Af F) σ J P g) (cj (Af F) σ (uT (Af F) σ J P g)) :=
      fun g => LinearMap.ext fun x => by rw [lin_levG_inv]
    simp only [e]
    exact continuous_levL_mat T P hI hcT
  unfold levG
  apply Continuous.subtype_mk
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hM.congr fun g => LinearMap.toMatrix'_toLin' _
  · exact hMi.congr fun g => LinearMap.toMatrix'_toLin' _

end Af

end PI.LevelKSplit.W.NCL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.IsClosedAsub

section

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r}

theorem mem_Asub {g : HA R σ J} : g ∈ Asub R σ J P ↔ (g ∈ Nsub R σ J P ∧
    (∀ w ∈ Wp R σ J P, lin R σ J g w = w) ∧
    (∀ b, lin R σ J g (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ) ∧
    (∀ b, lin R σ J g⁻¹ (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ)) := Iff.rfl

theorem Asub_le : Asub R σ J P ≤ Nsub R σ J P := fun _ hg => (mem_Asub.1 hg).1

end Gen

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}

theorem isClosed_Asub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : IsClosed (Asub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have hD : ∀ a a', hE σ J (P.e a') (P.f a) = if a = a' then 1 else 0 := fun a a' => by
    rw [hP.2.2.1 a' a]
    by_cases h : a = a'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hF : IsClosed (spanR (F := F) (Af F) P.f Set.univ : Set (Fin M → Af F ⊗[F] E)) :=
    PI.LevelKSplit.W.ExC.isClosed_spanR P.f P.e hD Set.univ
  have e : (Asub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∩
        ((⋂ w ∈ Wp (Af F) σ J P, {g : HA (Af F) σ J | lin (Af F) σ J g w = w}) ∩
        ((⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}) ∩
          (⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g⁻¹ (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_Asub
  rw [e]
  refine (PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP).2.1.inter
    ((isClosed_biInter fun w _ => ?_).inter ((isClosed_iInter fun b => ?_).inter
      (isClosed_iInter fun b => ?_)))
  · exact isClosed_eq (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const) continuous_const
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const)
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_inv continuous_const)

end Af

end PI.LevelKSplit.W.NCL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LeviPartAll

section

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NCL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct

theorem levi_part_all : LevPAll := by
  intro F E _ _ _ _ _ σ hσ M J _
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro hJ hinv r P T hP
  have H : (datR (Af F) σ J P T).Hyp := datR_hyp hinv hJ hP
  exact ⟨Asub (Af F) σ J P, levG hinv hJ hP, Asub_le, isClosed_Asub hJ hinv P T hP,
    continuous_levG hinv hJ P T hP,
    fun n hn => ⟨levG_mem hinv hJ hP n, levG_inv_mul hinv hJ hP n hn⟩,
    fun u hu hu1 => levi_inf_unipotent_eq_one hinv hJ hP u hu hu1,
    fun n hn m hm => unipotent_radical_normal n m hn hm,
    fun h hh u hu => H_comm_A H h u hh hu⟩

end PI.LevelKSplit.W.NCL
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit

section

@[expose] public section

theorem level_s_all_split : PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.Top6.levelSplitting_of_heisenberg_levi PI.LevelKSplit.W.NCH.heisenberg_parabolic_all
    PI.LevelKSplit.W.NCL.levi_part_all
end
end
