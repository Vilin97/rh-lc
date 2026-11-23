module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConervePropertyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRingsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRingsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
public import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.GrothendieckAbelian

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIso

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem hom_d_apply {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) :
    φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, HomologicalComplex.Hom.comm]

theorem nat_f_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, ε.naturality]

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contH_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro N M ε hε hN J _ _ D c hc n
  obtain ⟨hN1, hN2⟩ := hN J D c hc n
  have nat : ∀ (j : J) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      (ε.app c.pt).f m ((N.map (c.ι.app j)).f m x) = (M.map (c.ι.app j)).f m ((ε.app (D.obj j)).f m x) :=
    fun j m x => nat_f_apply ε (B := c.pt) (c.ι.app j) m x
  have dN : ∀ (j : J) (m m' : ℤ) (x : ((N).obj (D.obj j)).X m),
      (N.map (c.ι.app j)).f m' (((N).obj (D.obj j)).d m m' x) = ((N).obj c.pt).d m m' ((N.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (N).obj c.pt) (N.map (c.ι.app j)) m m' x
  have dM : ∀ (j : J) (m m' : ℤ) (x : ((M).obj (D.obj j)).X m),
      (M.map (c.ι.app j)).f m' (((M).obj (D.obj j)).d m m' x) = ((M).obj c.pt).d m m' ((M.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (M).obj c.pt) (M.map (c.ι.app j)) m m' x
  refine ⟨fun z hz => ?_, fun j w hw ⟨y, hy⟩ => ?_⟩
  · obtain ⟨c', y1, hc', h1⟩ := (hε c.pt).1 n z hz
    obtain ⟨j, w, y2, hw, h2⟩ := hN1 c' hc'
    refine ⟨j, (ε.app (D.obj j)).f n w, y1 + (ε.app c.pt).f (n - 1) y2, ?_, ?_⟩
    · rw [← hom_d_apply, hw, map_zero]
    · rw [← nat, h2, map_add (f := _), h1, map_add (f := _), hom_d_apply]
      abel
  · obtain ⟨c1, y1, hc1, h1⟩ := (hε (D.obj j)).1 n w hw
    have hcz : ((N).obj c.pt).d n (n + 1) ((N.map (c.ι.app j)).f n c1) = 0 := by
      rw [← dN, hc1, map_zero]
    obtain ⟨b, hb⟩ := (hε c.pt).2 n _ hcz ⟨y + (show ((M).obj c.pt).X (n - 1) from (M.map (c.ι.app j)).f (n - 1) y1), by
      rw [nat, h1, map_add (f := _), hy, map_add (f := _), dM]⟩
    obtain ⟨k, f, y2, h2⟩ := hN2 j c1 hc1 ⟨b, hb.symm⟩
    refine ⟨k, f, (ε.app (D.obj k)).f (n - 1) y2 - (M.map (D.map f)).f (n - 1) y1, ?_⟩
    have e1 : w = (ε.app (D.obj j)).f n c1 - ((M).obj (D.obj j)).d (n - 1) n y1 := by
      rw [h1]; abel
    rw [e1, map_sub, map_sub, ← nat_f_apply, h2, hom_d_apply, hom_d_apply]

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIsoStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.filteredColimitCohomology_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.contH_transport_quasiIso) | (exact GlobalTheory.EtC.contH_transport_quasiIso) | (intros; apply GlobalTheory.EtC.contH_transport_quasiIso  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximation

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LocSurjFT

theorem etFF_id (A : CommRingCat.{0}) : EtFF (𝟙 A) := by
  refine ⟨?_, ?_⟩
  · change (algebraMap A A).Etale
    exact RingHom.etale_algebraMap.2 inferInstance
  · change (algebraMap A A).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem locSurj_of_iso_on_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  intro N M ε F0 ι hF0 hι hneg hpos _hN hiso n A z hz
  rcases lt_trichotomy n 0 with hn | rfl | hn
  ·
    haveI := AddCommGrpCat.subsingleton_of_isZero (hneg n hn A)
    refine ⟨A, 𝟙 A, etFF_id A, 0, 0, by simp, Subsingleton.elim _ _⟩
  ·
    obtain ⟨x, rfl⟩ := ((hι A).2 z).1 hz
    obtain ⟨J, _, _, D, κ, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    obtain ⟨j, x0, hx0⟩ := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A κ) hc).1 x
    haveI := hiso (D.obj j) (hft j)
    set z0 : (M.obj (D.obj j)).X 0 := ι.app (D.obj j) x0 with hz0
    set c0 : (N.obj (D.obj j)).X 0 := (inv (ε.app (D.obj j))).f 0 z0 with hc0
    have hεc0 : (ε.app (D.obj j)).f 0 c0 = z0 := by
      have := congrArg (fun h => (h.f 0).hom z0) (IsIso.inv_hom_id (ε.app (D.obj j)))
      simpa [hc0] using this
    have hdz0 : (M.obj (D.obj j)).d 0 (0 + 1) z0 = 0 := ((hι (D.obj j)).2 z0).2 ⟨x0, rfl⟩
    have hdc0 : (N.obj (D.obj j)).d 0 (0 + 1) c0 = 0 := by
      have := congrArg (fun h => h.hom z0) ((inv (ε.app (D.obj j))).comm 0 (0 + 1))
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      rw [hc0, this, hdz0, map_zero]
    have h2 : (M.map (κ.app j)).f 0 z0 = ι.app A x := by
      have := ConcreteCategory.congr_hom (ι.naturality (κ.app j)) x0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [hz0, ← hx0]
      exact this.symm
    clear_value c0 z0
    refine ⟨A, 𝟙 A, etFF_id A, (N.map (κ.app j)).f 0 c0, 0, ?_, ?_⟩
    · have := ConcreteCategory.congr_hom ((N.map (κ.app j)).comm 0 (0 + 1)) c0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hdc0, map_zero] at this
      exact this
    · have h1 := ConcreteCategory.congr_hom (congrArg (fun h => h.f 0) (ε.naturality (κ.app j))) c0
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h1
      have h1' : (ε.app A).f 0 ((N.map (κ.app j)).f 0 c0) = (M.map (κ.app j)).f 0 ((ε.app (D.obj j)).f 0 c0) := h1
      rw [h1', hεc0, h2]
      simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, map_zero, add_zero]
      rfl
  ·
    obtain ⟨B, g, hg, y, hy⟩ := hpos n hn A z hz
    refine ⟨B, g, hg, 0, -y, by simp, ?_⟩
    rw [map_neg, hy]
    simp

end GlobalTheory.EtC.LocSurjFT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximationStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  first | (exact @GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (exact GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (intros; apply GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescent

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContAlg

theorem cohomology_filteredColimit_of_descent :
    ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro M F0 ι hF0 hι hneg hloc hdesc
  obtain ⟨N, ε, hN, hiso⟩ := GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType AbCx M
  have hterm := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).1
  have hcontN := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).2
  haveI : EtFF.IsStableUnderComposition := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.1.1.toIsStableUnderComposition

  have hNneg : ∀ n : ℤ, n < 0 → ∀ A, IsZero ((N.obj A).X n) := by
    intro n hn A
    obtain ⟨J, _, _, D, ιA, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    have hel := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N n)).1 (hterm n)) J D _ hc
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro x y
    suffices h : ∀ x : (N.obj A).X n, x = 0 by rw [h x, h y]
    intro x
    obtain ⟨j, w, rfl⟩ := hel.1 x
    have hz : IsZero ((N.obj (D.obj j)).X n) := by
      haveI := hiso (D.obj j) (hft j)
      have e : (N.obj (D.obj j)).X n ≅ (M.obj (D.obj j)).X n :=
        (HomologicalComplex.eval _ _ n).mapIso (asIso (ε.app (D.obj j)))
      exact (hneg n hn (D.obj j)).of_iso e
    have : w = 0 := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
      exact @Subsingleton.elim _ hz _ _
    subst this
    exact map_zero _
  have hqis := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent CommRingCat.{0} EtFF N M ε
    ⟨0, fun n hn U => ⟨hNneg n hn U, hneg n hn U⟩⟩
    (GlobalTheory.T.coveringsRefine_of_cechConerve_property CommRingCat.{0} EtFF _ (fun A B g hg n =>
      ⟨GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits (term N n) (term M n) (Functor.whiskerRight ε (HomologicalComplex.eval _ _ n)) (hterm n)
        (fun A' hA' => by
          haveI := hiso A' hA'
          change IsIso ((HomologicalComplex.eval _ _ n).map (ε.app A'))
          infer_instance)
        (fun A' B' g' hg' => hdesc A' B' g' hg' n) A B g hg,
       hdesc A B g hg n⟩))
    (GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation N M ε F0 ι hF0 hι hneg hloc hN hiso)
    (GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings N M ε F0 ι hF0 hι hneg hloc hN hiso)
  exact GlobalTheory.T.filteredColimitCohomology_transport_quasiIso N M ε hqis hcontN

end GlobalTheory.EtC.ContAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescentStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent : ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | exact GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | (intros; apply GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent <;> assumption)
end
end
