module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimage
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesLogChartStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSections
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLiftStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LiftedStalkMapGermAppLE
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.GroupTheory.Nilpotent
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SubsingletonCohOfDecomp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSectionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.cartier_operator_log_sections : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ → CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s)) (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  first | exact @_root_.GlobalTheory.cartierAt_atlas_inter | exact _root_.GlobalTheory.cartierAt_atlas_inter | (intros; apply _root_.GlobalTheory.cartierAt_atlas_inter <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLift

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem mem_inter_iff {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ inter U s ↔ ∀ i ∈ s, y ∈ U i := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [← ih]
    exact Iff.rfl

theorem decomp_of_isLifted (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p]
    {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι)
    (hn : n < p) (hL : IsLifted p (suppAll E) 𝒜.U 𝒜.x) : Decomp p 𝒜 := by
  intro G r hr a b hH
  exact GlobalTheory.T.cech_log_forms_frobenius_lift p (suppAll E) 𝒜.U 𝒜.x (inter 𝒜.U) G (p • G + ∑ c, r c • E c) hn 𝒜.gen
    (fun i => ((𝒜.chart i).chart _ (𝒜.gen i)).coord)
    (fun s _ y => mem_inter_iff 𝒜.U s y) hL
    (GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr).1
    (fun q s η hη => GlobalTheory.T.log_sections_differential_closed p 𝒜 G r hr q (inter 𝒜.U s) η hη)
    (fun s j hj γ hγ => GlobalTheory.T.cartier_operator_log_sections p 𝒜 G r hr s j hj γ hγ)
    a b hH

end GlobalTheory.LogDR
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLiftStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.frobenius_decomposition_of_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι), n < p → IsLifted p (suppAll E) 𝒜.U 𝒜.x → Decomp p 𝒜 := by
  first | exact @_root_.GlobalTheory.LogDR.decomp_of_isLifted | exact _root_.GlobalTheory.LogDR.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.LogDR.decomp_of_isLifted <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionAtlasModP

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.LogAtlas

theorem fnOf_coord_ne_zero {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {U : X.Opens} (h : genericPoint X ∈ U) {n : ℕ} {t : Fin n → Γ(X, U)}
    (ht : IsEtCoord f U t) (j : Fin n) : fnOf U h (t j) ≠ 0 := by
  intro h0
  have h1 : t j = 0 := fnOf_injective U h (h0.trans (map_zero _).symm)
  letI := (MvPolynomial.eval₂Hom (cstOn f U) t).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, U) := ht
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have h2 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_ne_zero (R := R) j))
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin n) R) • (1 : Γ(X, U)) =
      (MvPolynomial.X j : MvPolynomial (Fin n) R) • (0 : Γ(X, U)) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact (MvPolynomial.eval₂Hom_X' _ _ j).trans h1
  exact one_ne_zero (h2 h3)

theorem exists_div_of_sec {X : Scheme.{0}} [IsIntegral X] {M : LB X} (hM : M.IsLB) (τ : M.Sec) (c₀ : M.ι)
    (h₀ : genericPoint X ∈ M.U c₀) (hτ : fnOf _ h₀ (τ.f c₀) ≠ 0) :
    ∃ E : CartierDiv X, toPic E = cls M hM ∧ ∀ (c : M.ι) (y : X) (hy : y ∈ M.U c)
      (g : X.functionFieldˣ), (g : X.functionField) = fnOf _ (gen_mem hy) (τ.f c) → E.IsEqn y g := by
  have P := presents_ofLB hM c₀ h₀
  have hr : P.rat τ ≠ 0 := fun e => hτ (by rw [← P.rat_mul τ c₀ h₀, e, zero_mul])
  have Q := P.add_principal (Units.mk0 _ hr)
  refine ⟨_, Q.toPic_eq, fun c y hy g hg => ?_⟩
  have e : g = frameRat M c₀ h₀ c * Units.mk0 _ hr := Units.ext (by
    rw [hg, ← P.rat_mul τ c (gen_mem hy), Units.val_mul, Units.val_mk0, mul_comm])
  exact e ▸ Q.isEqn c y hy

theorem exists_div_of_chart {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Sp R} {d s : ℕ} {M : Fin s → LB X} (hM : ∀ i, (M i).IsLB) {τ : ∀ i, (M i).Sec}
    (C₀ : SncChart f d M τ) (h₀ : genericPoint X ∈ C₀.U) :
    ∃ E : Fin s → CartierDiv X, (∀ i, toPic (E i) = cls (M i) (hM i)) ∧
      ∀ (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (x : Fin d → X.functionFieldˣ),
        (∀ j, (x j : X.functionField) = fnOf C.U h (C.t j)) →
        ∀ i, ∀ y ∈ C.U, (E i).IsEqn y ((C.e i).elim 1 x) := by
  have key (C : SncChart f d M τ) (h : genericPoint X ∈ C.U) (i : Fin s) :
      fnOf _ (C.le i h) ((τ i).f (C.c i)) = fnOf C.U h (C.u i) * fnOf C.U h ((C.e i).elim 1 C.t) := by
    rw [← fnOf_resG (C.le i) h, C.eq i, map_mul]
  have H (i : Fin s) := exists_div_of_sec (hM i) (τ i) (C₀.c i) (C₀.le i h₀) (by
    rw [key C₀ h₀ i]
    refine mul_ne_zero (unitAt_fnOf h₀ h₀ _).ne_zero ?_
    rcases C₀.e i with _ | a
    · simp
    · exact fnOf_coord_ne_zero h₀ C₀.etale a)
  choose E hE hE' using H
  refine ⟨E, hE, fun C h x hx i y hy => ?_⟩
  have hu := unitAt_fnOf hy h (C.u i)
  have e : (((C.e i).elim 1 x : X.functionFieldˣ) : X.functionField) =
      fnOf C.U h ((C.e i).elim 1 C.t) := by
    rcases C.e i with _ | a
    · simp
    · exact hx a
  have h1 := hE' i (C.c i) y (C.le i hy) (Units.mk0 _ hu.ne_zero * (C.e i).elim 1 x) (by
    rw [Units.val_mul, Units.val_mk0, e]; exact (key C h i).symm)
  rw [h1.iff_unitAt, Units.val_mul, Units.val_mk0, div_mul_eq_div_div_swap, div_self (Units.ne_zero _),
    one_div]
  exact hu.inv

noncomputable def pullChart {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {X X' : Scheme.{0}}
    {f : X ⟶ Sp R} {f' : X' ⟶ Sp R'} {π : X' ⟶ X} (hP : IsPullback π f' f (spMap φ)) {d s : ℕ}
    {L : Fin s → LB X} {σ : ∀ i, (L i).Sec} (C : SncChart f d L σ) :
    SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) where
  U := π ⁻¹ᵁ C.U
  affine := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).1
  t := fun a => (π.app C.U).hom (C.t a)
  etale := (isEtCoord_baseChange R R' φ X X' f f' π C.U d C.t hP C.affine C.etale).2
  c := fun i => fun _ => C.c i
  le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
  e := C.e
  inj := C.inj
  u := fun i => Units.map (π.app C.U).hom (C.u i)
  eq := fun i => by
    show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
    rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
    rcases h : C.e i with _ | a
    · simp
    · simp

theorem exists_atlas_decomp : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∃ (m : ℕ) (E : Fin s → CartierDiv X) (𝒜 : SncAtlas E d (Fin m)), Decomp p 𝒜 ∧ ∀ i, toPic (E i) = CechPic.pull π (cls (L i) (h.isLB i)) := by
  classical
  intro p _ Y X _ g f π d _ hP hf hd s L σ h
  choose D hD using fun x : X => h.chart (π x)
  have hpr := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((π ⁻¹ᵁ (D x).U : X.Opens) : Set X))
    (fun x => (π ⁻¹ᵁ (D x).U).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hD x⟩)
  let ε := T.equivFin.symm
  let C : Fin T.card → SncChart g d L σ := fun k => D (ε k)
  have hgen (k) : genericPoint X ∈ (pullChart hP (C k)).U := gen_mem (x := ε k) (hD _)
  have hcov (y : X) : ∃ k, y ∈ (pullChart hP (C k)).U := by
    obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    obtain ⟨k, hk⟩ := ε.surjective ⟨z, hz⟩
    obtain rfl : (ε k : X) = z := congrArg Subtype.val hk
    exact ⟨k, hy⟩
  obtain ⟨k₀, -⟩ := hcov (genericPoint X)
  have : Nonempty (Fin T.card) := ⟨k₀⟩
  obtain ⟨E, hE, hE'⟩ := exists_div_of_chart (fun i => pull_isLB (h.isLB i) π) (pullChart hP (C k₀)) (hgen k₀)
  let x : Fin T.card → Fin d → X.functionFieldˣ := fun k j =>
    Units.mk0 _ (fnOf_coord_ne_zero (hgen k) (pullChart hP (C k)).etale j)
  let J : Fin T.card → Finset (Fin d) := fun k => Finset.univ.filter fun j => ∃ c, (C k).e c = some j
  have hJ (k j) : j ∈ J k ↔ ∃ c, (C k).e c = some j := by simp [J]
  have heq (k) := hE' (pullChart hP (C k)) (hgen k) (x k) (fun _ => rfl)
  have hlog (k) : IsLogChart (suppAll E) (pullChart hP (C k)).U (x k) (J k) := by
    refine GlobalTheory.T.etale_coordinates_log_chart p X f _ (hgen k) (pullChart hP (C k)).t (x k) (J k) _ (pullChart hP (C k)).affine
      (pullChart hP (C k)).etale (fun _ => rfl) fun y hy => ?_
    constructor
    · intro hy'
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hy'
      have h1 := (heq k c y hy).mem_supp_iff.1 hc
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField) at h1
      rcases he : (C k).e c with _ | a
      · rw [he] at h1
        exact (h1 (unitAt_one y)).elim
      · rw [he] at h1
        exact ⟨a, (hJ k a).2 ⟨c, he⟩, h1⟩
    · rintro ⟨j, hj, hu⟩
      obtain ⟨c, hc⟩ := (hJ k j).1 hj
      refine Set.mem_iUnion.2 ⟨c, (heq k c y hy).mem_supp_iff.2 ?_⟩
      change ¬ UnitAt y ((((C k).e c).elim 1 (x k) : X.functionFieldˣ) : X.functionField)
      rw [hc]
      exact hu
  let 𝒜 : SncAtlas E d (Fin T.card) :=
    { U := fun k => (pullChart hP (C k)).U
      x := x
      J := J
      affine := fun k => (pullChart hP (C k)).affine
      gen := hgen
      cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 (hcov y)
      chart := hlog
      snc := fun k => ⟨(C k).e, (C k).inj, hJ k, heq k⟩ }
  have : CharP X.functionField p := charP_of_injective_ringHom (Cartier.constFn f).injective p
  refine ⟨T.card, E, 𝒜, GlobalTheory.T.frobenius_decomposition_of_lift p 𝒜 hd ?_, fun i => (hE i).trans (CechPic.cls_pull (h.isLB i) π _)⟩
  refine DI.isLifted_of_sncCharts p Y X g f π hP L σ h.isLB C _ _ (fun _ => le_rfl) hgen x J
    (fun k l => ?_) (fun k l => (hJ k l).1) hlog
  exact congrArg (fun ψ : Γ(Y, (C k).U) ⟶ Γ(X, π ⁻¹ᵁ (C k).U) => fnOf _ (hgen k) (ψ.hom ((C k).t l)))
    (π.app_eq_appLE)

end GlobalTheory.LogAtlas
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KodairaVanishingModPSquared

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open GlobalTheory.Cartier GlobalTheory.LogDR

theorem GlobalTheory.CharPVanish.charp_of_lift : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X _ g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  obtain ⟨m, E, 𝒜, hdec, hE⟩ := GlobalTheory.LogAtlas.exists_atlas_decomp p Y X g f π d hpb hproj hdp s L σ h
  obtain ⟨M', hM'⟩ := GlobalTheory.Cartier.toPic_surjective (cls M hM)
  have hcan : GlobalTheory.Cartier.toPic (GlobalTheory.Cartier.canonical f d) = cls K.bundle K.isLB :=
    (GlobalTheory.Cartier.presents_canonical f d).toPic_eq.trans
      ((CechPic.cls_eq_iff _ _).2 (CanonLB.lbIso _ _))
  have hH : GlobalTheory.Cartier.toPic (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)
      = cls A hA.isLB := by

    simp only [map_sub, map_nsmul, map_sum, hM', hcan, hE]
    rw [heq]
    abel
  have hiso : LBIso (GlobalTheory.Cartier.toLB (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i)) A := by
    rw [← CechPic.cls_eq_iff (GlobalTheory.Cartier.isLB_toLB _) hA.isLB, ← GlobalTheory.Cartier.toPic_apply]
    exact hH
  have hampleH := IsAmpleLB.of_lbIso hA (GlobalTheory.Cartier.isLB_toLB _) hiso
  have key := GlobalTheory.CharPVanish.subsingleton_coh_of_decomp p X f d hproj hdp E 𝒜 hdec M'
    (r • M' - r • GlobalTheory.Cartier.canonical f d - ∑ i, b i • E i) r b hampleH hr hb (by abel) q hq
  refine GlobalTheory.Div.coh_subsingleton_of_cls_eq X (GlobalTheory.Cartier.toLB M') M (GlobalTheory.Cartier.isLB_toLB _) hM ?_ q key
  rw [← GlobalTheory.Cartier.toPic_apply, hM']
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KodairaVanishingModPSquaredStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.kodaira_vanishing_mod_p_squared : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) [IsIntegral X] (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @_root_.GlobalTheory.CharPVanish.charp_of_lift | exact _root_.GlobalTheory.CharPVanish.charp_of_lift | (intros; apply _root_.GlobalTheory.CharPVanish.charp_of_lift <;> assumption)
end
end
