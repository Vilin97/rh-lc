module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasisStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueDual
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCoverStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGeneratesStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueDualStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_glue_dualNumber : ∀ (S : Type) [CommRing S] (Y : Scheme.{0}) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ w : ∀ i, Sp (DualNumber (Localization.Away (h i))) ⟶ Y, (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → spMap (dualMap α) ≫ w i = spMap (dualMap β) ≫ w j) → ∃! w₀ : Sp (DualNumber S) ⟶ Y, ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = w i := by
  first | exact @GlobalTheory.Frames.existsUnique_glue_dual | exact GlobalTheory.Frames.existsUnique_glue_dual | (intros; apply GlobalTheory.Frames.existsUnique_glue_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TanBasisLocal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.TanBasisLocal

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp (DualNumber S) ⟶ Y}
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') : w = w' := by
  have key := GlobalTheory.Frames.existsUnique_glue_dual S Y n h hs
    (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') (by
      intro i j α β hα hβ
      rw [← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, ← dualMap_comp, ← dualMap_comp,
        hα, hβ])
  exact key.unique e (fun _ => rfl)

theorem base_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp S ⟶ Y}
    (e : ∀ i, spMap (algebraMap S (Localization.Away (h i))) ≫ w =
      spMap (algebraMap S (Localization.Away (h i))) ≫ w') : w = w' :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) h hs).openCover.hom_ext _ _ e

theorem fst_dual {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) :=
  RingHom.ext fun x => by
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem one_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left = (1 : Over.mk (spMap ψ ≫ x) ⟶ Xo.univ.t.G).left := by
  have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
      (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
    simp [Hom.one_def]
  rw [← e, Over.comp_left]
  rfl

theorem tan_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_ring, dualMap_alg, ← spMap_comp_ring,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_ring, fst_dual, ← spMap_comp_ring, Category.assoc, h2, one_pull]

theorem tan_local {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hv : ∀ i, IsTanAt (spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v)) : IsTanAt x v := by
  refine ⟨dual_ext hs fun i => ?_, base_ext hs fun i => ?_⟩
  · rw [← Category.assoc, (hv i).1, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring,
      dualMap_alg]
  · rw [one_pull, ← (hv i).2, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, fst_dual]

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [this]

theorem comb_exists {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ i, IsTanAt x (v i)) (a : Fin m → S) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x
  rw [Category.assoc, (hv i).1, ← Category.assoc, spMap_comp_ring, eps_alg]

theorem comb_pull_comp {S A C : Type} [CommRing S] [CommRing A] [CommRing C] {φ : S →+* A} {χ : S →+* C}
    (α : A →+* C) (hα : α.comp φ = χ) {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    {a : Fin m → A}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w)) :
    IsCombAt (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) (fun j => α (a j)) (spMap (dualMap χ) ≫ w) :=
  isCombAt_pull α (by rw [← Category.assoc, spMap_comp_ring, hα])
    (fun j => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα])
    (by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]) ha

theorem coeff_compat {S A B C : Type} [CommRing S] [CommRing A] [CommRing B] [CommRing C] {φ : S →+* A}
    {ψ : S →+* B} {χ : S →+* C} (α : A →+* C) (β : B →+* C) (hα : α.comp φ = χ) (hβ : β.comp ψ = χ)
    {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt x w) (hb : TanBasis (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k))
    {a : Fin m → A} {b : Fin m → B}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w))
    (hb' : IsCombAt (spMap ψ ≫ x) (fun k => spMap (dualMap ψ) ≫ v k) b (spMap (dualMap ψ) ≫ w)) :
    (fun j => α (a j)) = fun j => β (b j) := by
  have hB : TanBasis (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) := by
    have := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo _ _ α _ m _ hb
    have e1 : spMap α ≫ spMap φ ≫ x = spMap χ ≫ x := by rw [← Category.assoc, spMap_comp_ring, hα]
    have e2 : (fun k => spMap (dualMap α) ≫ spMap (dualMap φ) ≫ v k) = fun k => spMap (dualMap χ) ≫ v k :=
      funext fun k => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]
    rw [e1, e2] at this
    exact this
  exact (hB.2 _ (tan_pull χ hw)).unique (comb_pull_comp α hα ha) (comb_pull_comp β hβ hb')

theorem tanBasis_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, TanBasis (spMap (algebraMap S (Localization.Away (h i))) ≫ x) (fun k => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v k)) → TanBasis x v := by
  intro E _ _ _ H Dw l Xo S _ x n h hs m v hb
  have hv : ∀ k, IsTanAt x (v k) := fun k => tan_local hs fun i => (hb i).1 k
  have hb' : ∀ f : Set.range h, TanBasis (spMap (algebraMap S (Localization.Away f.1)) ≫ x)
      (fun k => spMap (dualMap (algebraMap S (Localization.Away f.1))) ≫ v k) := by
    rintro ⟨_, i, rfl⟩
    exact hb i
  refine ⟨hv, fun w hw => ?_⟩
  choose d hd hdu using fun f : Set.range h =>
    (hb' f).2 _ (tan_pull (algebraMap S (Localization.Away f.1)) hw)
  have compat : ∀ (k : Fin m) (f g : Set.range h),
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : S)) f.1 g (d f k) =
        IsLocalization.Away.awayToAwayLeft g.1 f (d g k) := by
    intro k f g
    let α : Localization.Away f.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayRight f.1 g
    let β : Localization.Away g.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayLeft g.1 f
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 s
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 s
    exact congrFun (coeff_compat α β hα hβ hw (hb' f) (hd f) (hd g)) k
  choose c hc hcu using fun k => Localization.existsUnique_algebraMap_eq_of_span_eq_top (Set.range h) hs
    (fun f => d f k) (compat k)
  refine ⟨c, ?_, fun a ha => funext fun k => hcu k _ fun f => ?_⟩
  · obtain ⟨w', hw'⟩ := comb_exists hv c
    have : w' = w := dual_ext hs fun i => by
      let f : Set.range h := ⟨h i, i, rfl⟩
      have h1 := isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl hw'
      have e : (fun j => algebraMap S (Localization.Away f.1) (c j)) = d f := funext fun j => hc j f
      rw [e] at h1
      exact comb_unique h1 (hd f)
    exact this ▸ hw'
  · exact congrFun (hdu f _ (isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl ha)) k

end GlobalTheory.TanBasisLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointsGluePrincipalCover

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.Glue

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (f g : Sp (DualNumber S) ⟶ Y)
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ f =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) : f = g := by
  have := GlobalTheory.T.existsUnique_glue_dualNumber S Y n h hh (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ g) (by
    intro i j α β hα hβ
    rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, dual_comp, dual_comp, hα, hβ])
  exact this.unique e fun _ => rfl

theorem exists_lift {S : Type} [CommRing S] {n : ℕ} {h : Fin n → S}
    (hh : Ideal.span (Set.range h) = ⊤) (p : Sp S) :
    ∃ (i : Fin n) (p' : Sp (Localization.Away (h i))), spMap (algebraMap S (Localization.Away (h i))) p' = p := by
  have hp : ∃ i, h i ∉ (show PrimeSpectrum S from p).asIdeal := by
    by_contra hc
    push Not at hc
    apply (show PrimeSpectrum S from p).isPrime.ne_top
    rw [eq_top_iff, ← hh, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hc i
  obtain ⟨i, hi⟩ := hp
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away (h i)) (h i)
  have : (show PrimeSpectrum S from p) ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (h i)))) := by
    rw [hr]; exact hi
  obtain ⟨p', hp'⟩ := this
  exact ⟨i, p', hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem secBC_unique {S T : Type} [CommRing S] [CommRing T] {φ : S →+* T} {a : S} {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} {s : LB.Sec (PPx x)} {t t' : LB.Sec (PPx x')} (h₁ : SecBC φ a x x' s t)
    (h₂ : SecBC φ a x x' s t') : t = t' := by
  obtain ⟨p₁, s₁, f₁, a₁⟩ := h₁
  obtain ⟨p₂, s₂, f₂, a₂⟩ := h₂
  have e : p₁ = p₂ := by
    apply pullback.hom_ext
    · exact f₁.trans f₂.symm
    · exact s₁.trans s₂.symm
  subst e
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht'⟩ := t'
  congr 1
  funext i
  exact (a₁ i (chart_le p₁ s₁ i)).symm.trans (a₂ i (chart_le p₁ s₁ i))

theorem secBC_transport {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T] {φ : S →+* T} {ψ : S' →+* T}
    {x : Sp S ⟶ Xo.X} {x' : Sp S' ⟶ Xo.X} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')} {w w' : Sp T ⟶ Xo.X}
    (hw : w = w') {r : LB.Sec (PPx w)} (h₁ : SecBC φ 1 x w s r) (h₂ : SecBC ψ 1 x' w s' r)
    (t : LB.Sec (PPx w')) (ht : SecBC φ 1 x w' s t) : SecBC ψ 1 x' w' s' t := by
  subst hw
  rw [secBC_unique ht h₁]
  exact h₂

def algOf {K S A B : Type} [CommRing K] [CommRing S] [CommRing A] [CommRing B] [Algebra K S] [Algebra S A]
    [Algebra S B] [Algebra K A] [Algebra K B] [IsScalarTower K S A] [IsScalarTower K S B] (α : A →+* B)
    (hα : α.comp (algebraMap S A) = algebraMap S B) : A →ₐ[K] B :=
  { α with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply K S A, IsScalarTower.algebraMap_apply K S B, ← hα]
      rfl }

end GlobalTheory.Frames.Glue


open GlobalTheory.Frames.Glue in
theorem GlobalTheory.Frames.frPt_glue : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∀ (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ y : ∀ i, FrPt Xo c (Localization.Away (h i)), (∀ i, (y i).x = spMap (algebraMap S (Localization.Away (h i))) ≫ x) → (∀ i j (α : Localization.Away (h i) →ₐ[c.F] Localization.Away (h i * h j)) (β : Localization.Away (h j) →ₐ[c.F] Localization.Away (h i * h j)), α.toRingHom.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.toRingHom.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ z, FrMap α (y i) z → FrMap β (y j) z) → ∃ y₀ : FrPt Xo c S, y₀.x = x ∧ ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y₀ (y i) := by
  intro hB E _ _ _ H Dw l Xo c S _ _ x hx n h hh y hy hov
  classical

  have ovl : ∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j))
      (β : Localization.Away (h j) →+* Localization.Away (h i * h j)),
      α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) →
      β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) →
      ∃ z : FrPt Xo c (Localization.Away (h i * h j)),
        z.x = spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x ∧
        (∀ τ k, z.u τ k = spMap (dualMap α) ≫ (y i).u τ k) ∧ (∀ τ k, z.u τ k = spMap (dualMap β) ≫ (y j).u τ k) ∧
        SecBC α 1 _ _ (y i).s z.s ∧ SecBC β 1 _ _ (y j).s z.s := by
    intro i j α β hα hβ
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c _ _ (algOf (K := c.F) α hα) (y i)
    have hz' := hov i j (algOf α hα) (algOf β hβ) hα hβ z hz
    have e₁ := ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ (y i)).2.2 z).1 hz
    have e₂ := ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ (y j)).2.2 z).1 hz'
    refine ⟨z, ?_, e₁.2.1, e₂.2.1, e₁.2.2, e₂.2.2⟩
    rw [e₁.1, hy i, ← Category.assoc, sp_comp, ← hα]
    rfl

  have nf : ∀ i, ∃ ov u tan eig basis s gen,
      y i = ⟨spMap (algebraMap S (Localization.Away (h i))) ≫ x, ov, u, tan, eig, basis, s, gen⟩ := by
    intro i
    have hi := hy i
    generalize y i = w at hi
    obtain ⟨wx, ov, u, tan, eig, basis, s, gen⟩ := w
    dsimp only at hi
    subst hi
    exact ⟨ov, u, tan, eig, basis, s, gen, rfl⟩
  choose ov u tan eig basis s gen hyy using nf
  obtain rfl : y = fun i => ⟨_, ov i, u i, tan i, eig i, basis i, s i, gen i⟩ := funext hyy
  dsimp only at ovl

  have hu : ∀ τ k, ∃ w₀ : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w₀ = u i τ k := by
    intro τ k
    refine (GlobalTheory.T.existsUnique_glue_dualNumber S _ n h hh (fun i => u i τ k) ?_).exists
    intro i j α β hα hβ
    obtain ⟨z, -, h₁, h₂, -⟩ := ovl i j α β hα hβ
    exact (h₁ τ k).symm.trans (h₂ τ k)
  choose u₀ hu₀ using hu
  have eig₀ : ∀ τ k, IsEigAt c τ (u₀ τ k) := by
    intro τ k a
    refine dual_ext hh _ _ fun i => ?_
    rw [← Category.assoc, hu₀, eig i τ k a, ← hu₀ τ k i, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
      dual_eps, ← IsScalarTower.algebraMap_apply]
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  have tb : TanBasis x (fun j => u₀ (e j).1 (e j).2) := by
    refine GlobalTheory.TanBasisLocal.tanBasis_local E H Dw l Xo S x n h hh _ _ fun i => ?_
    have := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c _ _ (u i) _ e (tan i) (eig i)).1 (basis i)
    simpa only [hu₀] using this
  have tan₀ : ∀ τ k, IsTanAt x (u₀ τ k) := by
    intro τ k
    have := tb.1 (e.symm ⟨τ, k⟩)
    dsimp only at this
    rw [e.apply_symm_apply] at this
    exact this
  have basis₀ := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c S x u₀ _ e tan₀ eig₀).2 tb

  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.T.existsUnique_glue_sections_principal_cover E H Dw l Xo S x n h hh s (by
    intro i j α β hα hβ t ht
    obtain ⟨z, hz, -, -, h₁, h₂⟩ := ovl i j α β hα hβ
    exact secBC_transport hz h₁ h₂ t ht)).exists
  have nz : SecNZ x s₀ := by
    intro p
    obtain ⟨i, p', rfl⟩ := exists_lift hh p
    exact (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S _ _ x _ rfl s₀ (s i) (hs₀ i) p').1
      (GlobalTheory.T.fibreSectionNowhereZero_of_generates hB E H Dw l Xo _ _ (s i) (gen i) p')
  refine ⟨⟨x, hx, u₀, tan₀, eig₀, basis₀, s₀, GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hB E H Dw l Xo S x s₀ nz⟩, rfl, fun i => ?_⟩
  refine ((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c _ _ _ _).2.2 _).2 ⟨rfl, fun τ k => (hu₀ τ k i).symm, hs₀ i⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointsGluePrincipalCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoints_glue_principal_cover : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∀ (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ y : ∀ i, FrPt Xo c (Localization.Away (h i)), (∀ i, (y i).x = spMap (algebraMap S (Localization.Away (h i))) ≫ x) → (∀ i j (α : Localization.Away (h i) →ₐ[c.F] Localization.Away (h i * h j)) (β : Localization.Away (h j) →ₐ[c.F] Localization.Away (h i * h j)), α.toRingHom.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.toRingHom.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ z, FrMap α (y i) z → FrMap β (y j) z) → ∃ y₀ : FrPt Xo c S, y₀.x = x ∧ ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y₀ (y i) := by
  first | exact @GlobalTheory.Frames.frPt_glue | exact GlobalTheory.Frames.frPt_glue | (intros; apply GlobalTheory.Frames.frPt_glue <;> assumption)
end
end
