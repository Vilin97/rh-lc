module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.LocalRing.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Field
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.KrullDimension.Zero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FiltByPositiveWeightOfTwoCharacterExtensionStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositiveStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeightStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCoefficientFieldOfFiniteLocalPadic

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem exists_coefficientField_of_finite_local_padic : ∀ {l : ℕ} [Fact l.Prime] (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B], ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E) (_ : FiniteDimensional ℚ_[l] E) (_ : Algebra E B) (_ : IsScalarTower ℚ_[l] E B) (π : B →ₐ[E] E), ∀ a, π a = 0 → IsNilpotent a := by
  intro l _ B _ _ _ _
  have hart : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  let g : B →ₐ[ℚ_[l]] ResidueField B := Ideal.Quotient.mkₐ ℚ_[l] (maximalIdeal B)
  have het : Algebra.FormallyEtale ℚ_[l] (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable ℚ_[l] (ResidueField B)
  have hker : RingHom.ker (g : B →+* ResidueField B) = maximalIdeal B := Ideal.mk_ker
  have hnil : IsNilpotent (RingHom.ker (g : B →+* ResidueField B)) := by
    rw [hker]
    exact (IsArtinianRing.isNilpotent_jacobson_bot (R := B)).imp fun n h => by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  let s : ResidueField B →ₐ[ℚ_[l]] B :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℚ_[l] _) g hsurj hnil
  have hs : ∀ x, g (s x) = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ g hsurj hnil x
  letI alg : Algebra (ResidueField B) B := s.toRingHom.toAlgebra
  have tower : IsScalarTower ℚ_[l] (ResidueField B) B := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap ℚ_[l] B r = s (algebraMap ℚ_[l] (ResidueField B) r)
    exact (s.commutes r).symm
  let π : B →ₐ[ResidueField B] ResidueField B :=
    { (g : B →+* ResidueField B) with
      commutes' := fun x => hs x }
  refine ⟨ResidueField B, inferInstance, inferInstance, inferInstance, alg, tower, π, ?_⟩
  intro a ha
  have hmem : a ∈ maximalIdeal B := by
    rw [← hker]
    exact ha
  exact Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hmem

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvalues

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκc hine x hx hxc hcr y z hzy hy
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have cd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκc i) (hκc j)
  have ined : ∀ i j g, φ g ∈ Iq l →
      (κ i / κ j) g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) := fun i j g hg => by
    rw [MonoidHom.div_apply, hine g hg i, hine g hg j, zpow_sub, div_eq_mul_inv]
  have crk : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκc i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hine g hg, smul_eq_mul]
  have crd : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (cd i j)) ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) fun g hg v => by
      rw [chRep_apply, ined i j g hg, smul_eq_mul]
  have hxf := (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκc 0) (hκc 1) x hx hxc (crk 0) (crk 1)).1 hcr
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  rw [eM] at hzy ⊢
  set M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' with hM
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have hin02 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 2) g = cycA l l B (φ g) ^ (2 * (e : ℤ)) := fun g hg => by
    rw [ined 0 2 g hg, w0, w2]; congr 1; ring
  have hin12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B (φ g) ^ (e : ℤ) := fun g hg => by
    rw [ined 1 2 g hg, w1, w2]; congr 1; ring
  have pM : Positive φ (resCoef E M) := ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM,
    GlobalTheory.T.filtBy_positiveWeight_of_two_character_extension φ hφ π hπ (κ 0 / κ 2) (κ 1 / κ 2) (cd 0 2) (cd 1 2) (2 * (e : ℤ)) e (by omega)
      (by exact_mod_cast he) hin02 hin12 x hx'⟩
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E M) (resCoef E (chRep (κ 1 / κ 2))) cM
    (contAction_chRep (cd 1 2)) pM (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcM : c ∈ UpperTheory.V.Loc.finiteCocycles φ M := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous z := hzy.1.fst
  have hcc : Continuous fun g => (c g).1 := hcM.1.1.fst
  have hzm : ∀ g h, z (g * h) =
      z g + ((((κ 0 / κ 2) g : Bˣ) : B) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h =>
    congrArg Prod.fst (hzy.2 g h)
  have hcm : ∀ g h, (c (g * h)).1 =
      (c g).1 + ((((κ 0 / κ 2) g : Bˣ) : B) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcM.1.2 g h)
  have hd : z - (fun g => (c g).1) ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hzc.sub hcc, fun g h => ?_⟩
    simp only [Pi.sub_apply, hzm, hcm, chRep_apply]
    ring
  have hd' : z - (fun g => (c g).1) ∈ Z1 (resCoef E (chRep (κ 0 / κ 2))) := hd
  obtain ⟨hcχ, pχ⟩ := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02
    (resCoef E (chRep (κ 0 / κ 2))) (fun g v => rfl)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ (resCoef E (chRep (κ 0 / κ 2))) hcχ pχ
  have hinj : Function.Injective (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp Subtype.val_injective
  have hD : H0dual ((cycA l l E).comp φ) (resCoef E (chRep (κ 0 / κ 2))) = ⊥ := by
    have hopen : IsOpen ((φ.range : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [MonoidHom.coe_range]; exact hφ.isOpen_range
    obtain ⟨s, ⟨⟨g, rfl⟩, hs⟩, hfo⟩ := ((cycInertia l).2 φ.range hopen).2
    refine eq_bot_iff.2 fun F hF => ?_
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun v => ?_
    have h1 := hF g v
    simp only [MonoidHom.comp_apply] at h1
    have hχg : (((κ 0 / κ 2) g : Bˣ) : B) = algebraMap E B (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) := by
      rw [hin02 g hs, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; rfl
    have h2 : F (resCoef E (chRep (κ 0 / κ 2)) g v) = (((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) * F v := by
      change F ((((κ 0 / κ 2) g : Bˣ) : B) * v) = _
      rw [hχg, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [h2] at h1
    have hne : cycA l l E (φ g) ^ (2 * (e : ℤ)) ≠ cycA l l E (φ g) := by
      intro h
      have h3 : cyc l l (φ g) ^ (2 * (e : ℤ) - 1) = 1 := by
        apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) hinj
        rw [map_zpow, map_one]
        change cycA l l E (φ g) ^ (2 * (e : ℤ) - 1) = 1
        rw [zpow_sub_one, h, mul_inv_cancel]
      exact hfo (isOfFinOrder_iff_zpow_eq_one.2 ⟨_, by omega, h3⟩)
    have h4 : ((((cycA l l E (φ g)) ^ (2 * (e : ℤ)) : Eˣ) : E) - (cycA l l E (φ g) : E)) * F v = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (Units.ext (sub_eq_zero.1 h5)) hne
    · simpa using h5
  rw [hD, finrank_bot, add_zero] at hdim
  have hle : UpperTheory.V.Loc.finiteCocycles φ (resCoef E (chRep (κ 0 / κ 2))) ≤ Z1 (resCoef E (chRep (κ 0 / κ 2))) :=
    fun c h => h.1
  haveI := hfin
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim.symm
  have hdf : z - (fun g => (c g).1) ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 2)) := by
    rw [← heq] at hd'
    exact (z1fMap φ (resCoef E (chRep (κ 0 / κ 2))) (chRep (κ 0 / κ 2))).2 LinearMap.id (fun _ _ => rfl) _ hd'
  have inl : ∀ g v, LinearMap.inl E B B (chRep (κ 0 / κ 2) g v) = M g (LinearMap.inl E B B v) := fun g v => by
    simp [hM, characterExtensionRep_apply, chRep_apply]
  have h1 := (z1fMap φ (chRep (κ 0 / κ 2)) M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l]) inl _ hdf
  have h2 := add_mem h1 hcM
  convert h2 using 1
  funext g
  ext <;> simp [hc2]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvaluesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.ordinary_lift_local_iso : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h), Continuous x → IsCr φ (ext2 (κ 0) (κ 1) x hx) → ∀ y z : G → B, (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → (fun g => (z g, y g)) ∈ finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
  first | exact @GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient | exact GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient | (intros; apply GlobalTheory.crystalline_cocycle_twisted_extension_of_quotient <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriCrys

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ finiteCocycles φ (chRep (κ 0 / κ 1)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκ hI x y z ρ hz hρ hxf hyf
  have hxc : Continuous x := hxf.1.1
  have hyc : Continuous y := hyf.1.1
  have hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => hxf.1.2 g h
  have crκ : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hI g hg i, smul_eq_mul]
  have hext : IsCr φ (ext2 (κ 0) (κ 1) x hx) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ (κ 0) (κ 1) (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf
  have hmat : ∀ g h (i j : Fin 3), (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ((ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B)) i j := fun g h i j => by
    rw [map_mul, Units.val_mul]
  have hZ : (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
    refine ⟨hz.prodMk hyc, fun g h => ?_⟩
    have h02 := hmat g h 0 2
    have h12 := hmat g h 1 2
    rw [hρ, hρ, hρ] at h02 h12
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12

    have hu : ((κ 2 g : Bˣ) : B) * (((κ 2 g)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    have hv : ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    rw [twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]
    ext
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h02 - ((z (g * h) - z g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((z (g * h) - z g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h12 - ((y (g * h) - y g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((y (g * h) - y g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 1 g : Bˣ) : B) * y h)) * hv
  exact (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2
    (GlobalTheory.T.ordinary_lift_local_iso hP φ hφ π hπ e he κ hκ hI x hx hxc hext y z hZ hyf)

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPush

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  intro hP l _ G _ _ _ φ hφ B' _ _ _ _ _ _ _ _ _ B _ _ _ _ q e he κ hκ hI x y z ρ hz hρ hx hy σ hσ hqx hqy

  obtain ⟨E', _, _, _, _, _, π', hπ'⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B'
  obtain ⟨E, _, _, _, _, _, π, hπ⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B
  letI : Algebra ℤ_[l] E' := ((algebraMap ℚ_[l] E').comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] B := ((algebraMap ℚ_[l] B).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B

  have hqc : Continuous (q : B' → B) := IsModuleTopology.continuous_of_linearMap (q.toLinearMap)
  let qm : B' →* B := (q : B' →+* B)
  let κB : Fin 3 → G →* Bˣ := fun i => (Units.map qm).comp (κ i)
  have hqcyc : ∀ h : GQ l, Units.map qm (cycA l l B' h) = cycA l l B h := by
    intro h
    apply Units.ext
    change q (algebraMap ℤ_[l] B' _) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] _)
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B', q.commutes]

  have hw01 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 1) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 0, hI g hg 1]
    simp [wt1]
  have hw12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 1, hI g hg 2]
    simp [wt1]
  have hcdiv : ∀ i j, Continuous fun g => (((κ i / κ j) g : B'ˣ) : B') := by
    intro i j
    have : (fun g => (((κ i / κ j) g : B'ˣ) : B')) = fun g => (κ i g : B') * (κ j g⁻¹ : B') := by
      funext g
      rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul, ← map_inv]
    rw [this]
    exact (hκ i).mul ((hκ j).comp continuous_inv)
  have he : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he

  obtain ⟨cx, hcx, hxf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 0 / κ 1) (hcdiv 0 1) e he hw01 σ hσ x hx
  obtain ⟨cy, hcy, hyf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 1 / κ 2) (hcdiv 1 2) e he hw12 σ hσ y hy
  have push : ∀ (i j : Fin 3) (c : G → B'), c ∈ finiteCocycles φ (chRep (κ i / κ j)) →
      (fun g => q (c g)) ∈ finiteCocycles φ (chRep (κB i / κB j)) := by
    intro i j c hc
    refine (z1fMap φ (chRep (κ i / κ j)) (chRep (κB i / κB j))).2 q.toLinearMap (fun g v => ?_) c hc
    show q ((((κ i / κ j) g : B'ˣ) : B') * v) = (((κB i / κB j) g : Bˣ) : B) * q v
    rw [map_mul]
    congr 1
    simp only [κB, MonoidHom.div_apply, MonoidHom.comp_apply, ← _root_.map_div, Units.coe_map]
    rfl
  have hxB : (fun g => q (x g)) ∈ finiteCocycles φ (chRep (κB 0 / κB 1)) := by
    have h := push 0 1 _ hxf
    convert h using 2 with g
    simp [hqx _ (hcx g)]
  have hyB : (fun g => q (y g)) ∈ finiteCocycles φ (chRep (κB 1 / κB 2)) := by
    have h := push 1 2 _ hyf
    convert h using 2 with g
    simp [hqy _ (hcy g)]
  refine GlobalTheory.tri_crys hP φ hφ π hπ e (by exact_mod_cast he) κB (fun i => hqc.comp (hκ i)) ?_ (fun g => q (x g))
    (fun g => q (y g)) (fun g => q (z g)) ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ) (hqc.comp hz) ?_ hxB hyB
  · intro g hg i
    simp only [κB, MonoidHom.comp_apply, hI g hg i, map_zpow, hqcyc]
  · intro g
    rw [MonoidHom.comp_apply]
    show (ρ g : Matrix (Fin 3) (Fin 3) B').map q = _
    rw [hρ g]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, κB, qm]

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPushStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_rank_three_crystalline_after_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  first | exact @GlobalTheory.tri_crys_push | exact GlobalTheory.tri_crys_push | (intros; apply GlobalTheory.tri_crys_push <;> assumption)
end
end
