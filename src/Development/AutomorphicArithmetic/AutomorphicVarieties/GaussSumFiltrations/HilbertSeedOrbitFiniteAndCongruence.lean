module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsInGScalarMulAndAbsNormDetMulAbsFEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.StabilizerEqScalarMulCongruenceMulFinset

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.StabFin

variable {F : Type} [Field F] [NumberField F]

theorem cover_gen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U : Subgroup G)
    (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (g : G) :
    ∃ C : Finset G, ∀ k ∈ K, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ U := by
  have hc : IsCompact ((fun k : G => g * k * g⁻¹) '' (K : Set G)) := hK.image (by fun_prop)
  obtain ⟨C, hC⟩ := hc.elim_finite_subcover (fun c : G => (fun x => x * c⁻¹) ⁻¹' (U : Set G))
    (fun c => hU.preimage (by fun_prop)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨C, fun k hk => ?_⟩
  obtain ⟨c, hc, h⟩ := Set.mem_iUnion₂.1 (hC ⟨k, hk, rfl⟩)
  exact ⟨c, hc, h⟩

theorem cover (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ C : Finset (GL (Fin 2) (Af F)), ∀ k ∈ KLev F 2 1, ∃ c ∈ C, g * k * g⁻¹ * c⁻¹ ∈ KLev F 2 N :=
  cover_gen _ _ (isCompact_KLev le_rfl) (isOpen_KLev hN) g

theorem toFin_scalar (η : Fˣ) : toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap F (Af F)).toMonoidHom η) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toFin, Matrix.GeneralLinearGroup.scalar]

theorem det_toFin (δ : GL (Fin 2) F) : (toFin δ).val.det = algebraMap F (Af F) δ.val.det := by
  rw [RingHom.map_det]; rfl

theorem exists_unit {x : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x = 1) (hx : x ≠ 0) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = x := by
  have H := (GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.2.2
  have h1 : IsIntegral ℤ x := (H x).1 fun w => (h w).le
  have h2 : IsIntegral ℤ x⁻¹ := (H _).1 fun w => by rw [map_inv₀, h w, inv_one]
  refine ⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx)
  · exact Subtype.ext (inv_mul_cancel₀ hx)

theorem det_unit {g k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 1) {δ : GL (Fin 2) F} (h : toFin δ = g * k * g⁻¹) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) = δ.val.det := by
  obtain ⟨H1, -, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine exists_unit (fun w => ?_) δ.det_ne_zero
  have e : (toFin δ).val.det = k.val.det := by
    rw [h, Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  rw [← H4, ← det_toFin, e]
  exact ((H1 k).1 hk).2 w

theorem integral_of_mem {x : F} (h : algebraMap F (Af F) x ∈ Ohat F) : IsIntegral ℤ x := by
  obtain ⟨-, -, -, H4, H5⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H5 x).1 fun w => ?_
  rw [← H4]
  exact (Subring.mem_iInf.1 h w : pLoc F w (algebraMap F (Af F) x) ∈ w.adicCompletionIntegers F)

theorem inGam_of_mem {N : ℕ} (hN : 0 < N) {γ : GL (Fin 2) F} (hd : γ.val.det = 1) (h : toFin γ ∈ KLev F 2 N) :
    InGam N γ := by
  obtain ⟨h1, -, h3⟩ := mem_KLev.1 h
  refine ⟨hd, integral_of_mem (h1 0 0), integral_of_mem (h1 0 1), integral_of_mem ?_, integral_of_mem (h1 1 1)⟩
  obtain ⟨y, hy, e⟩ := h3 1 0
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e' : algebraMap F (Af F) (γ.val 1 0) = (N : Af F) * y := by
    rw [← e]; simp [toFin]
  have : algebraMap F (Af F) (γ.val 1 0 / N) = y := by
    rw [div_eq_inv_mul, map_mul, e', ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]
  rwa [this]

theorem unit_scalar_mem (ε : (𝓞 F)ˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map (algebraMap F (Af F)).toMonoidHom (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε)) ∈ KLev F 2 1 := by
  obtain ⟨-, H2, -, H4, -⟩ := GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F
  refine (H2 _ 0 (fun w => ?_) (fun w => by simp)).2
  refine (H4 (algebraMap (𝓞 F) F ε) w).trans ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ε.isUnit)

theorem invariants [IsTotallyReal F] (g : GL (Fin 2) (Af F)) {N : ℕ} (hN : 0 < N) :
    ∃ I : Finset (F × GL (Fin 2) (Af F)), ∀ γ, Stab g γ → ∃ i ∈ I, ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N := by
  classical
  obtain ⟨⟨Y, hY⟩, E, hE⟩ := GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares F
  obtain ⟨C, hC⟩ := cover g hN
  have hb : ∀ y : (Af F)ˣ, ∃ b : GL (Fin 2) F, ∀ δ : GL (Fin 2) F, ∀ k ∈ KLev F 2 1,
      toFin δ = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹) →
        ∃ k' ∈ KLev F 2 1, toFin (δ * b⁻¹) = g * k' * g⁻¹ := fun y => by
    by_cases h : ∃ b : GL (Fin 2) F, ∃ k ∈ KLev F 2 1,
      toFin b = Matrix.GeneralLinearGroup.scalar (Fin 2) y * (g * k * g⁻¹)
    · obtain ⟨b, k₀, hk₀, e⟩ := h
      refine ⟨b, fun δ k hk e' => ⟨k * k₀⁻¹, mul_mem hk (inv_mem hk₀), ?_⟩⟩
      rw [map_mul, map_inv, e, e', Matrix.GeneralLinearGroup.scalar_commute y,
        Matrix.GeneralLinearGroup.scalar_commute y]
      group
    · exact ⟨1, fun δ k hk e => absurd ⟨δ, k, hk, e⟩ h⟩
  choose b hb using hb
  refine ⟨(Y ×ˢ E ×ˢ C).image fun t => (((t.2.1 : 𝓞 F) : F) * (b t.1).val.det, t.2.2 * toFin (b t.1)), ?_⟩
  rintro γ ⟨-, z, u, hu, e⟩
  obtain ⟨y, hy, ξ, v, -, hv, rfl⟩ := hY z
  have hvK := ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.1 v 0 hv (fun w => by simp)).2
  obtain ⟨k, hk, ek⟩ := hb y (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ) _ (mul_mem hvK hu) (by
    rw [map_mul, eq_mul_inv_of_mul_eq e, map_inv, map_inv, toFin_scalar, map_mul, map_mul, ← mul_assoc g,
      ← Matrix.GeneralLinearGroup.scalar_commute v g]
    group)
  obtain ⟨ε, hε⟩ := det_unit hk ek
  obtain ⟨e₀, he₀, η, rfl⟩ := hE ε
  obtain ⟨c, hc, hcK⟩ := hC _ (mul_mem (unit_scalar_mem η⁻¹) hk)
  refine ⟨_, Finset.mem_image.2 ⟨(y, e₀, c), by simp [hy, he₀, hc], rfl⟩,
    Units.map (algebraMap (𝓞 F) F).toMonoidHom η⁻¹ * ξ⁻¹, ?_, ?_⟩
  · have h1 : (Matrix.GeneralLinearGroup.scalar (Fin 2) ξ⁻¹ * γ).val.det =
        ((e₀ * η ^ 2 : (𝓞 F)ˣ) : 𝓞 F) * (b y).val.det := by
      rw [hε, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel_right]
    rw [map_mul, mul_assoc, Units.val_mul, Matrix.det_mul, h1, ← Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.det_scalar]
    have hη : ((η : 𝓞 F) : F) ≠ 0 := by simp
    simp
    field_simp
  · convert hcK using 1
    rw [map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)), mul_assoc _ _ γ, map_mul toFin, toFin_scalar, ← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute _ g,
      mul_assoc _ g k, mul_assoc _ (g * k), ← ek, map_mul toFin _ (b y)⁻¹, map_inv toFin]
    group

theorem finite_index : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  classical
  intro F _ _ _ g N hN
  obtain ⟨I, hI⟩ := invariants g hN
  let P : GL (Fin 2) F → F × GL (Fin 2) (Af F) → Prop := fun γ i => Stab g γ ∧ ∃ η : Fˣ,
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ).val.det = i.1 ∧
        toFin (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ) * i.2⁻¹ ∈ KLev F 2 N
  have hr : ∀ i, ∃ τ, (∃ γ, P γ i) → P τ i := fun i => by
    by_cases h : ∃ γ, P γ i
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine ⟨(I.filter fun i => ∃ γ, P γ i).image r, fun τ hτ => ?_, fun γ hγ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hτ
    exact (hr i (Finset.mem_filter.1 hi).2).1
  · obtain ⟨i, hi, η, h1, h2⟩ := hI γ hγ
    have hP : ∃ γ, P γ i := ⟨γ, hγ, η, h1, h2⟩
    obtain ⟨-, η', h1', h2'⟩ := hr i hP
    refine ⟨η⁻¹ * η', Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) η' * r i)⁻¹, r i,
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hi, hP⟩), inGam_of_mem hN ?_ ?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, h1, ← h1', ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one]
    · convert mul_mem h2 (inv_mem h2') using 1
      rw [map_mul toFin (_ * γ), map_inv]
      group
    · rw [mul_comm η⁻¹, map_mul, map_inv, Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc,
        Matrix.GeneralLinearGroup.scalar_commute η']
      rw [← Matrix.GeneralLinearGroup.scalar_commute η' (r i), mul_assoc, mul_assoc, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute η' (r i)]
      group

end GlobalTheory.HilbertThetaSeries.StabFin

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) (Af F)) (N : ℕ), 0 < N → ∃ T : Finset (GL (Fin 2) F), (∀ τ ∈ T, Stab g τ) ∧ ∀ γ, Stab g γ → ∃ (η : Fˣ) (γ₀ : GL (Fin 2) F), ∃ τ ∈ T, InGam N γ₀ ∧ γ = Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ := by
  first | exact @GlobalTheory.HilbertThetaSeries.StabFin.finite_index | exact GlobalTheory.HilbertThetaSeries.StabFin.finite_index | (intros; apply GlobalTheory.HilbertThetaSeries.StabFin.finite_index <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSeedOrbitFiniteAndCongruence

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) : reAt v x = rhom x v := by
  simp only [reAt, rhom]
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem scal_comm {R : Type} [CommRing R] (z : Rˣ) (A : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * A = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mul_comm]

theorem norm_rat {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (q : ℚ) : ‖ι.symm (q : ℂ)‖ = ‖(q : ℚ_[p])‖ := by
  rw [map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]

theorem fermat {p : ℕ} [hp : Fact p.Prime] (r : ℚ) (hr : ‖(r : ℚ_[p])‖ = 1) :
    ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ ≤ (p : ℝ)⁻¹ := by
  set x : ℤ_[p] := ⟨r, hr.le⟩ with hxdef
  have hxn : ‖x‖ = 1 := hr
  have hx : IsUnit x := PadicInt.isUnit_iff.mpr hxn
  have h0 : PadicInt.toZMod x ≠ 0 := by
    intro h
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
    rw [PadicInt.ker_toZMod] at this
    exact (IsLocalRing.mem_maximalIdeal x).mp this hx
  have h1 : x ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one h0, sub_self]
  have h2 : ‖x ^ (p - 1) - 1‖ < 1 := PadicInt.mem_nonunits.mp h1
  have h3 : ‖x ^ (p - 1) - 1‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using h2
  have h4 : ‖x ^ (p - 1) - 1‖ = ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [← h4]; simpa using h3

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem tp_mul {a b : F} (ha : TP a) (hb : TP b) : TP (a * b) := fun v => by
  rw [reAt_eq, map_mul, Pi.mul_apply, ← reAt_eq, ← reAt_eq]; exact mul_pos (ha v) (hb v)

theorem tp_one : TP (1 : F) := fun v => by rw [reAt_eq, map_one]; exact one_pos

theorem stab_one (g : GL (Fin 2) (Af F)) : Stab g (1 : GL (Fin 2) F) :=
  ⟨by simpa using (tp_one : TP (1 : F)), 1, 1, (KLev F 2 1).one_mem, by simp⟩

theorem stab_mul (g : GL (Fin 2) (Af F)) (γ γ' : GL (Fin 2) F) (h : Stab g γ) (h' : Stab g γ') : Stab g (γ * γ') := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  obtain ⟨ht', z', u', hu', he'⟩ := h'
  refine ⟨?_, z' * z, u * u', (KLev F 2 1).mul_mem hu hu', ?_⟩
  · rw [Units.val_mul, Matrix.det_mul]; exact tp_mul ht ht'
  · rw [map_mul, mul_assoc, he', ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) z'), he, map_mul]
    simp only [mul_assoc]

theorem stab_inv (g : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) (h : Stab g γ) : Stab g γ⁻¹ := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  refine ⟨?_, z⁻¹, u⁻¹, (KLev F 2 1).inv_mem hu, ?_⟩
  · have h1 : γ.val.det * (γ⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    intro v
    have hv := congrArg (fun x => rhom x v) h1
    simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply] at hv
    have hp := ht v
    rw [reAt_eq] at hp ⊢
    exact (pos_iff_pos_of_mul_pos (by rw [hv]; exact one_pos)).mp hp
  · rw [map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹), he]
    simp only [map_inv]
    group

theorem absF_ne_zero (y : (Af F)ˣ) : absF y ≠ 0 := by
  classical
  unfold absF
  rw [finprod_def]
  split_ifs with h
  · rw [Finset.prod_ne_zero_iff]
    intro w _
    rw [norm_ne_zero_iff]
    exact ((Units.map (pLoc F w).toMonoidHom y).ne_zero)
  · exact one_ne_zero

end GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness in
theorem orbit_seed_finite_congr : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  intro F _ _ _ p _ ι hp2 δ hδ θ hθ y hy
  have hk : Even (p - 1) := (Fact.out : p.Prime).even_sub_one hp2
  obtain ⟨-, hsl, hscal, htS, -⟩ := GlobalTheory.T.hilbert_slash_rational_matrix_properties F (p - 1) θ
  have hpos : ∀ γ : GL (Fin 2) F, TP γ.val.det → Pos (toInf γ) := fun γ h => (hsl γ).1.mpr h

  have hsc : ∀ (η : Fˣ) (γ : GL (Fin 2) F), TP γ.val.det →
      sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ)) θ = sl (p - 1) (toInf γ) θ := by
    intro η γ h
    rw [map_mul, htS η]
    exact (hscal hk _ _ (hpos γ h)).2
  refine ⟨?_, ?_, stab_one _, fun γ γ' h h' => ⟨stab_mul _ γ γ' h h', stab_inv _ γ h⟩⟩
  ·
    obtain ⟨N, hN, hlev⟩ := hθ.lev
    obtain ⟨T, hT, hcov⟩ := GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset F (aff y 0) N hN
    refine ((Polynomial.nthRoots 8 (1 : ℂ)).toFinset.finite_toSet.image2
      (fun ζ τ => ζ • sl (p - 1) (toInf τ) θ) T.finite_toSet).subset ?_
    rintro f ⟨γ, hγ, rfl⟩
    obtain ⟨η, γ₀, τ, hτ, hγ₀, rfl⟩ := hcov γ hγ
    obtain ⟨ζ, hζ, hζe⟩ := hlev γ₀ hγ₀
    refine ⟨ζ, ?_, τ, hτ, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (by norm_num)).mpr hζ
    have hdet0 : γ₀.val.det = 1 := hγ₀.1
    have hp0 : Pos (toInf γ₀) := hpos γ₀ (by rw [hdet0]; exact tp_one)
    have hpτ : Pos (toInf τ) := hpos τ (hT τ hτ).1
    have hd : TP (γ₀ * τ).val.det := by
      rw [Units.val_mul, Matrix.det_mul, hdet0, one_mul]; exact (hT τ hτ).1
    symm
    show sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ)) θ = ζ • sl (p - 1) (toInf τ) θ
    rw [mul_assoc, hsc η _ hd, map_mul,
      (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp0 hpτ).2.2.2.1, (hsl γ₀).2, hdet0, hζe]
    simp only [map_one, Rat.cast_one, abs_one, Real.one_rpow, Complex.ofReal_one, one_smul]
    exact ((slash_add_smul_pow F (p - 1) 1 (toInf τ) θ θ ζ).2.2.2.2.1)
  ·
    intro γ hγ γ' hγ'
    obtain ⟨htp, z, u, hu, he⟩ := hγ
    obtain ⟨hmulG, -, hcmp⟩ := GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq F p δ hδ
    obtain ⟨η, r, hG, hr0, hr1, hnorm⟩ := hcmp y y z γ u hy hy htp hu he
    set γ₁ := Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ with hγ₁
    have hN : |((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| = (r : ℝ) ^ 2 :=
      mul_right_cancel₀ (absF_ne_zero y) hnorm
    have hpow : (|((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| ^ (((p - 1 : ℕ) : ℝ) / 2) : ℝ) = (r : ℝ) ^ (p - 1) := by
      rw [hN, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]
      congr 1; ring
    have hp1 : Pos (toInf γ₁) := hpos γ₁ hG.2.2.2.2.2
    have hp' : Pos (toInf γ') := hpos γ' hγ'.2.2.2.2.2
    set c : ℂ := (((r ^ (p - 1) : ℚ) : ℝ) : ℂ) with hc
    have e1 : sl (p - 1) (toInf γ) θ = c • sl0 (p - 1) (toInf γ₁) θ := by
      rw [← hsc η γ htp, (hsl γ₁).2, hpow, hc]; push_cast; rfl
    have hS := hθ.one (γ₁ * γ') (hmulG γ₁ γ' hG hγ')
    set F0 := sl0 (p - 1) (toInf (γ₁ * γ')) θ with hF0
    have e2 : sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1 = c • (F0 - 1) + (fun _ => c - 1) := by
      rw [e1, (slash_add_smul_pow F (p - 1) 1 (toInf γ') (sl0 (p - 1) (toInf γ₁) θ) θ c).2.1,
        ← (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp1 hp').2.2.1, ← map_mul, hF0]
      funext w; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]; ring
    have hcn : ‖ι.symm c‖ = 1 := by
      rw [hc, Complex.ofReal_ratCast, norm_rat, Rat.cast_pow, norm_pow, hr1, one_pow]
    have hc1 : ‖ι.symm (c - 1)‖ ≤ (p : ℝ)⁻¹ := by
      have : c - 1 = (((r ^ (p - 1) - 1 : ℚ)) : ℂ) := by rw [hc]; push_cast; ring
      rw [this, norm_rat]; push_cast; exact fermat r hr1
    obtain ⟨-, -, hA, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c hS hS
    obtain ⟨-, -, -, -, -, hB⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ (c - 1) hS hS
    obtain ⟨hsum, -, -, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hA hB
    rw [e2]
    refine (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hsum hS).2.2.2.1 ?_
    rw [hcn, one_mul]
    exact max_le le_rfl hc1

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.hilbert_seed_orbit_finite_and_congruence : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | exact GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | (intros; apply GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr <;> assumption)
end
end
