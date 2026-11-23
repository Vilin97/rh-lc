module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsAdelicFourierExpansionOfLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsIsHolAdelicLiftOfEvenWeightSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsOrbitAverageOfSeedPowersWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsSeedThetaLatticeFixedPointFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SystemCuspInfinityComponentCongrOne

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FormSystemOfFinitelyManyStabilizerForms

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SysOfStab

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma pos_iff (γ : GL (Fin 2) F) : Pos (toInf γ) ↔ TP γ.val.det := by
  have h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det
      = rhom γ.val.det := by
    rw [RingHom.map_det]; rfl
  unfold Pos TP
  rw [h]
  rfl

lemma scal_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext1
  exact ((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm

def Rel (g g' : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g' * u

lemma tp_mul {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) : TP (γ * γ').val.det := by
  rw [← pos_iff] at h h' ⊢
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1

lemma tp_inv {γ : GL (Fin 2) F} (h : TP γ.val.det) : TP (γ⁻¹).val.det := by
  rw [← pos_iff] at h ⊢
  rw [map_inv]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1

lemma tp_one : TP (1 : GL (Fin 2) F).val.det := by
  rw [← pos_iff, map_one]
  intro v
  simp

lemma sl_mul (k : ℕ) {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) (f : Hn F → ℂ) :
    sl k (toInf (γ * γ')) f = sl k (toInf γ') (sl k (toInf γ) f) := by
  rw [← pos_iff] at h h'
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1

lemma sl_one (k : ℕ) (f : Hn F → ℂ) : sl k (toInf (1 : GL (Fin 2) F)) f = f := by
  have h := (pos_iff (1 : GL (Fin 2) F)).2 tp_one
  rw [map_one]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2

lemma Rel.symm {g g' : GL (Fin 2) (Af F)} {γ : GL (Fin 2) F} (h : Rel g g' γ) : Rel g' g γ⁻¹ := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  refine ⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩
  have e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹ := by
    rw [e]; group
  rw [e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc,
    scal_comm]
  group

lemma Rel.trans {g g' g'' : GL (Fin 2) (Af F)} {γ γ' : GL (Fin 2) F} (h : Rel g g' γ) (h' : Rel g' g'' γ') :
    Rel g g'' (γ' * γ) := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  obtain ⟨hγ', z', u', hu', e'⟩ := h'
  refine ⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩
  rw [map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]
  group

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  intro F _ _ _ k Y f hcov hf
  let P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop := fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ
  let y : GL (Fin 2) (Af F) → (Af F)ˣ := fun g => Classical.epsilon (P g)
  have hy : ∀ g, P g (y g) := by
    intro g
    apply Classical.epsilon_spec (p := P g)
    obtain ⟨γ, hγ, y, hyY, u, hu, e⟩ := hcov g
    exact ⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩
  have hyeq : ∀ g g' γ, Rel g g' γ → y g = y g' := by
    intro g g' γ h
    have : P g = P g' := by
      funext x
      exact propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩
    simp only [y, this]
  choose c hc using fun g => (hy g).2
  let Ψ : GL (Fin 2) (Af F) → Hn F → ℂ := fun g => sl k (toInf (c g)) (f (y g))
  have key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g := by
    intro g g' γ h
    have h1 : Rel g (aff (y g) 0) (c g' * γ) := by
      rw [hyeq g g' γ h]; exact h.trans (hc g')
    have h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹) := (hc g).symm.trans h1
    have h3 := (hf _ (hy g).1).2.2 _ h2
    simp only [Ψ]
    rw [← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]
    conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]
  refine ⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩
  · have h := (hf _ (hy g).1).1
    exact ((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · have h := (hf _ (hy g).1).2.1
    exact ((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · exact key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
  · have := key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩
    rw [← this, sl_one]
  · have := key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1
      ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
    rw [← this, sl_one]
  · obtain ⟨hγ, z, u, hu, e⟩ := hc g
    exact ⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩

end GlobalTheory.HilbertThetaSeries.SysOfStab

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Gl2AdelicDoubleCosetDecompositionTotallyReal

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Reps

variable {F : Type} [Field F] [NumberField F]

theorem aff_mul_aff {R : Type} [CommRing R] (a b : Rˣ) : aff a 0 * aff b 0 = aff (a * b) (0 : R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (η : Fˣ) : toFin (aff η 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom η) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem det_aff' {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

theorem exists_sl_aff (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ Matrix.GeneralLinearGroup.det σ = 1 ∧
      g = toFin σ * (aff y 0 * u) := by
  set y := Matrix.GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff', hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply, Complex.ofReal_re]

theorem TP_mul {x y : F} (hx : TP x) (hy : TP y) : TP (x * y) := fun v => by
  have := mul_pos (hx v) (hy v)
  rw [reAt_eq, reAt_eq] at this; rw [reAt_eq, map_mul]; exact this

theorem TP_inv {x : F} (hx : TP x) : TP x⁻¹ := fun v => by
  have := inv_pos.2 (hx v)
  rw [reAt_eq] at this; rw [reAt_eq, map_inv₀]; exact this

end GlobalTheory.HilbertThetaSeries.Reps

open GlobalTheory.HilbertThetaSeries.Reps in
theorem GlobalTheory.HilbertThetaSeries.finite_reps : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  intro F _ _ _ p hp δ hδ
  classical
  obtain ⟨Y0, hY0⟩ := (GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F).1
  choose ξf hξf using (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).2 δ hδ
  set ι := Units.map (algebraMap F (Af F)).toMonoidHom with hι
  refine ⟨Y0.image (fun y => ι (ξf y) * y), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact (hξf y).2
  · intro g
    obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl_aff (KLev F 2 1) (isOpen_KLev le_rfl) g
    obtain ⟨y0, hy0, ξ, u0, hξ, hu0, hy⟩ := hY0 y
    have hK := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 u0 0 hu0 (fun w => by simp)
    refine ⟨aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹, ?_, ι (ξf y0) * y0, Finset.mem_image_of_mem _ hy0, aff u0 0 * u, mul_mem hK.1 hu, ?_⟩
    · have hd : (aff (ξ⁻¹ * ξf y0) 0 * σ⁻¹ : GL (Fin 2) F).val.det = ((ξ⁻¹ * ξf y0 : Fˣ) : F) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hσ, det_aff', inv_one, mul_one]
      rw [hd, Units.val_mul]
      exact TP_mul (by simpa using TP_inv hξ) (hξf y0).1
    · rw [e, map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, toFin_aff, ← mul_assoc, aff_mul_aff, aff_mul_aff, hy]
      congr 2
      simp only [map_mul, map_inv, hι]
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) ξ = a
      generalize (Units.map (algebraMap F (Af F)).toMonoidHom) (ξf y0) = b
      rw [mul_comm a⁻¹ b, mul_assoc b, ← mul_assoc a⁻¹, ← mul_assoc a⁻¹, inv_mul_cancel, one_mul, ← mul_assoc]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∃ Y : Finset (Af F)ˣ, (∀ y ∈ Y, AtP p δ y) ∧ ∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_reps | exact GlobalTheory.HilbertThetaSeries.finite_reps | (intros; apply GlobalTheory.HilbertThetaSeries.finite_reps <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQOfSmallSubOne

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_of_small_sub_one {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    {r : ℝ} (hr : r < 1) {g : Hn F → ℂ} (hg : Small ι r (g - 1)) :
    ∃ a, HasQ g a ∧ ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
  classical
  obtain ⟨b, hb, hs⟩ := hg
  have h1 := (hasQ_lin F _ _ b b 1 hb hb).2.2.2
  have h2 := (hasQ_lin F _ _ _ _ 1 hb h1).1
  have e : (g - 1 + fun _ : Hn F => (1 : ℂ)) = g := by funext z; simp
  rw [e] at h2
  refine ⟨_, h2, ?_, ?_⟩
  · simpa using (hs 0).trans_lt hr
  · simpa using (hs 1).trans_lt hr

theorem hilbertOne : UpperTheory.V.Published.HilbertOne := by
  intro F _ _ _ p _ hp2 ι
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hp).1
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree F p ι hp2 δ hδ
  obtain ⟨Y, hY, hrep⟩ := GlobalTheory.T.gl2_adelic_double_coset_decomposition_totally_real F p hp δ hδ
  have hav : ∀ y : (Af F)ˣ, ∃ N : ℕ, y ∈ Y → ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨N, hN⟩ := GlobalTheory.T.exists_orbit_average_of_seed_powers_weight F p ι hp2 δ hδ θ hθ y (hY y hy)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose n hn using hav
  refine ⟨Y.sup n, fun k _ hk => ?_⟩
  obtain ⟨m, rfl⟩ := hk
  rw [mul_assoc]
  set k := (p - 1) * (p ^ Y.sup n * m) with hkdef
  have hf : ∀ y : (Af F)ˣ, ∃ f : Hn F → ℂ, y ∈ Y → Comp ι δ k (aff y 0) f := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨f, hf⟩ := hn y hy (p ^ Y.sup n * m) ((pow_dvd_pow p (Finset.le_sup hy)).mul_right m)
      exact ⟨f, fun _ => hf⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose f hf using hf
  obtain ⟨Ψ, hΨ, hval⟩ := GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms F k Y (fun y => ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f y) hrep (fun y hy =>
    ⟨(HolKeep.main F k _ _ _ (hf y hy).hol (hf y hy).hol).2.1, (Growth.gr_closed F k _ _ _ (hf y hy).gr (hf y hy).gr).2.1,
      fun γ hγ => by rw [(slash_add_smul_pow F k 0 _ _ (f y) _).2.2.2.2.1, (hf y hy).inv γ hγ]⟩)
  have hev : Even k := (hp.even_sub_one hp2).mul_right _
  obtain ⟨φ, hl, hφ⟩ := GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system F k hev Ψ hΨ
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hone : ∀ y : (Af F)ˣ, ∃ a, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) a ∧
      ‖ι.symm (a 0) - 1‖ < 1 ∧ ‖ι.symm (a 1)‖ < 1 := by
    intro y
    obtain ⟨γ, z, hγ, y', hy', u, hu, h1, h2⟩ := hval (aff y 0)
    exact hasQ_of_small_sub_one ι hlt
      (GlobalTheory.T.system_cusp_infinity_component_congr_one F p ι hp2 δ hδ k (dvd_mul_right _ _) Ψ hΨ y y' z (f y') (hY y' hy') (hf y' hy').one γ u hγ hu h1 h2)
  choose a ha h0 h1 using hone
  obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_adelic_fourier_expansion_of_lift F k Ψ φ.1 a hΨ hl ha
  refine ⟨φ, fun y => a y 0, c, hφ, hc, h0, fun 𝔪 h𝔪 => ?_⟩
  obtain ⟨y, hy⟩ := hc' 𝔪 h𝔪
  rw [hy]
  exact h1 y

end GlobalTheory.HilbertThetaSeries
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne

section

@[expose] public section

namespace UpperTheory.V

theorem Published.exists_hilbertModularForm_congr_one : Published.HilbertOne := GlobalTheory.HilbertThetaSeries.hilbertOne

theorem Lit.oneUse : Lit.OneUse := Lit.oneUse_of Published.exists_hilbertModularForm_congr_one

end UpperTheory.V
end
end
