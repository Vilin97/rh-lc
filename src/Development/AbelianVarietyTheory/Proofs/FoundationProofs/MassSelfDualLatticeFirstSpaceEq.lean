module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CosetGroupEquiv
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabiliserCardinality
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfMembership
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TrivialColumnStabiliser
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DoubleCosetCount

section

@[expose] public section

namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation

open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

theorem card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by
  have hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y},
      ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1 := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, h⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hd.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    refine Eq.trans ?_ (DoubleCoset.out_eq' (H := Γ) (K := U) d)
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩
  choose κ hκ using hex
  rw [← Nat.card_prod, Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) :
      K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)
  · rintro ⟨d, s, hs⟩ ⟨e, t, ht⟩ h
    have hs' := ((mem_stab Γ K y _).1 hs).1
    have ht' := ((mem_stab Γ K y _).1 ht).1
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hde : d = e := by
      apply Subtype.ext
      rw [← hκ d, ← hκ e]
      exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩
    subst hde
    have h2 : s⁻¹ * t ∈ stab Γ U (y * κ d) := by
      refine (mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩
      convert h1 using 1
      group
    rw [hfree, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y := by
        obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1
          (DoubleCoset.out_eq' (H := Γ) (K := U) (DoubleCoset.mk Γ U (y * k))).symm
        symm
        exact (@DoubleCoset.eq _ _ Γ K _ _).2
          ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩
      obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 (hκ ⟨_, hd⟩)
      have hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹ := by
        generalize (κ ⟨_, hd⟩ : G) = m at h ⊢
        rw [show (k : G) = y⁻¹ * (y * k) by group, h]
        group
      have hs : a ∈ stab Γ K y := by
        refine (mem_stab Γ K y _).2 ⟨ha, ?_⟩
        rw [hk]
        exact K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)
      refine ⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      convert hu using 1
      group

theorem doubleCosetCount : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp

end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerGroupMap

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Proof.StabilizerGroupMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem bc_inclE_injective (D : D7) :
    Function.Injective
      (bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
        GL (Fin D.R.k) D.host.E →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective
  have h2 := congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab
  simpa [bc] using h2

theorem stabGroup_eq_map (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y =
      (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).map
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm

theorem stabGroup_eq_bot_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥ ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y = ⊥ := by
  rw [stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]

theorem at_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    (GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D, GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivialAt D Lv u := by
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2),
    fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩

theorem columnStabilisersTrivial_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.ColumnStabilisersTrivial ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivial :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u

end GlobalTheory.Proof.StabilizerGroupMap

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassSelfDualLatticeFirstSpaceEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ColClassNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open GlobalTheory.IndefiniteRowSideFullHecke

theorem card_eq_index_mul_mass {G : Type} [Group G] (Γ U K : Subgroup G) (m : ℝ) (hUK : U ≤ K)
    (hidx : U.relIndex K ≠ 0) (hm : ClassesDoubleCosets.CosetMass Γ K m)
    (hfree : ∀ x γ : G, γ ∈ Γ → x⁻¹ * γ * x ∈ U → γ = 1) :
    (Nat.card (ClassSet Γ U) : ℝ) = (U.relIndex K : ℝ) * m := by
  obtain ⟨hfin, hst, hsum⟩ := hm
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  have e : ∀ y : G, StabiliserCardinality.stab Γ K y ≃ stabAt Γ K y := fun y =>
    { toFun := fun γ => ⟨⟨γ.1, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).1⟩, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).2⟩
      invFun := fun γ => ⟨γ.1.1, (StabiliserCardinality.mem_stab Γ K y _).2 ⟨γ.1.2, γ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  have h := (GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount G Γ U K hUK ⟨hidx⟩
    (fun y => have := hst y; Finite.of_equiv _ (e y).symm)
    (fun x => (Subgroup.eq_bot_iff_forall _).2 fun γ hγ =>
      hfree x γ ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).1 ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).2)
    _ hs).2
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', ← hsum _ hs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [one_div, Nat.card_congr (e _)]

section Lattice

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem exists_lattice (N : Submodule (𝓞 E) (Fin R.k → E)) (hfin : Module.Finite (𝓞 E) N)
    (hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤)
    (hdual : dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E))) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧ sp.crdLat0 M = N := by
  let e : (sp.X 0).V ≃ₗ[𝓞 E] (Fin R.k → E) := sp.crd0.restrictScalars (𝓞 E)
  have hmem : ∀ x, x ∈ N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) ↔ sp.crd0 x ∈ N := fun x => by
    rw [Submodule.mem_map_equiv]; rfl
  refine ⟨N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V), ?_, ?_, ?_⟩
  · exact Submodule.IsLattice.of_fg E ((Module.Finite.iff_fg.1 hfin).map _)
  · ext x
    rw [hmem, ← SetLike.mem_coe (p := N), ← hdual]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one, hmem, sp.hermitianForm_base_coordinates, dualSet, Set.mem_setOf_eq,
      RingHom.mem_range]
    constructor
    · intro h y hy
      have := h (sp.crd0.symm y) (by simpa using hy)
      simpa using this
    · intro h y hy
      exact h _ hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      exact ⟨sp.crd0.symm y, (hmem _).2 (by simpa using hy), by simp⟩

end Lattice

theorem idx_pos (D : D7) : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
  have h : ∀ g k : ℕ, g.Prime → 0 < idxColLoc g k := by
    intro g k hg
    haveI : NeZero g := ⟨hg.ne_zero⟩
    haveI : Nonempty {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} :=
      ⟨⟨1, fun i j h => by simp [h.ne'], fun i => by simp⟩⟩
    exact div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  exact mul_pos (pow_pos (h _ _ (D.host.g_prime 0)) _) (pow_pos (h _ _ (D.host.g_prime 1)) _)

theorem mass_selfDualLattice_firstSpace_eq (D : D7) : letI := D.host.cmStar
    ∀ M : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E M →
      Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT M → Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT M = massI D D.R.k := by
  letI := D.host.cmStar
  intro M hM hu
  rw [← D.sp.rank0]
  exact GlobalTheory.genusMassStd D { D.sp.X 0 with L0 := M, standardTuple_isLattice := hM, baseLattice_isUnimodular := hu } (D.sp.X_sig 0)
    (baseSpace_posDef _ _ D.sp)

theorem classNumber (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (hcos : ClassesDoubleCosets.ClassesAsDoubleCosets) (hstab : ColumnStabiliser.ColStabTrivial)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  letI := D.host.cmStar
  intro hg hs u hT
  obtain ⟨-, N, ⟨hfin, hspan, hdual, -⟩, -, -, hUK⟩ := hover D Lv u hT
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice D.sp N hfin hspan hdual
  have hidx := hindex D Lv u hs hT _ ⟨hfin, hspan, hdual.symm⟩ hUK
  have hm := hcos.2 D Lv u M hM hu
  rw [mass_selfDualLattice_firstSpace_eq D M hM hu] at hm
  have hrel := Subgroup.relIndex_subgroupOf (H := SelfDualLatticeIndex.levelU D Lv u)
    (SelfDualLatticeIndex.stabHat_le D (D.sp.crdLat0 M))
  have hne : (SelfDualLatticeIndex.levelU D Lv u).relIndex (SelfDualLatticeIndex.stabHat D (D.sp.crdLat0 M)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    exact (mul_pos (idx_pos D) (SelfDualLatticeIndex.factorT_pos D u)).ne hidx
  have h := card_eq_index_mul_mass _ ((Lv u).U.subgroupOf _) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hne) hm (by
      intro x γ hγ hx
      have h1 := ColumnStabiliser.map_colStab D Lv u x
      rw [hstab D Lv u hg hs x, Subgroup.map_bot] at h1
      have h2 : γ.1 ∈ (⊥ : Subgroup _) := by
        rw [h1]
        exact ⟨hγ, ⟨_, hx, by simp [mul_assoc]⟩⟩
      exact Subtype.ext (Subgroup.mem_bot.1 h2))
  rw [Nat.card_eq_of_bijective _ (Lv u).y_bij]
  refine h.trans ?_
  rw [mul_assoc (massI D D.R.k), mul_comm (massI D D.R.k)]
  exact congrArg (· * massI D D.R.k) ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hidx)

theorem classNumber_of_index (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber hover hindex (GlobalTheory.Proof.CosetGroupEquiv.massAsCosetSum_iff.1 GlobalTheory.Proof.TotallyDefiniteMass.massAsCosetSum)
    (GlobalTheory.Proof.StabilizerGroupMap.columnStabilisersTrivial_iff.1 GlobalTheory.Proof.EqOneOfMembership.columnStabilisersTrivial) D Lv

end GlobalTheory.ColClassNumber

end
end
end
