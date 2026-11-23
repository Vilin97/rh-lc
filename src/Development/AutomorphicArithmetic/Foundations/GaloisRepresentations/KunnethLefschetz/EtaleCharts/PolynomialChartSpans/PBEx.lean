module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatUnique
public import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.USelf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.InjField
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.OntoField

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatOne

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a : V ⟶ WP B), GMat B a a 1 := by
  intro K _ W Z Y q i π D d B V a x
  obtain ⟨U, α, a₁, hx, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  refine ⟨U, α, α, a₁, a₁, hx, ha, ha, ?_⟩
  have hc : U.ι ≫ a ≫ cP B = a₁ ≫ (oW B α).ι := by
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    rw [← Category.assoc, show U.ι ≫ a = a₁ ≫ wI B α from ha, Category.assoc, h]
  have h1 : (1 : Matrix (Fin d) (Fin d) Γ(V, ⊤)).map U.ι.appTop.hom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1]
  refine locMatOne B α _ fun y => ?_
  rw [hc, Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (a₁ y).2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsG

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsG :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), ∃ g : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B), a ≫ cP B = b ≫ cP B → GL (Fin d) Γ(V, ⊤), (∀ {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), g (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc]) = Matrix.GeneralLinearGroup.map s.appTop.hom (g a b h)) ∧ (∀ {V : Scheme.{0}} (a b k : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B) (h' : b ≫ cP B = k ≫ cP B), g b k h' * g a b h = g a k (h.trans h')) ∧ ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B), GMat B a b (g a b h : Matrix (Fin d) (Fin d) Γ(V, ⊤)) := by
  intro K _ W Z Y q i π D d B
  have hinv : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (h : a ≫ cP B = b ≫ cP B),
      (gMatExists B b a h.symm).choose * (gMatExists B a b h).choose = 1 := fun a b h =>
    gMatUnique B a a _ _
      (gMatComp B a b a _ _ h (gMatExists B a b h).choose_spec (gMatExists B b a h.symm).choose_spec)
      (gMatOne B a)
  refine ⟨fun {V} a b h => ⟨(gMatExists B a b h).choose, (gMatExists B b a h.symm).choose,
    hinv b a h.symm, hinv a b h⟩, ?_, ?_, ?_⟩
  · intro V' V s a b h
    apply Units.ext
    exact gMatUnique B (s ≫ a) (s ≫ b) _ _ (gMatExists B (s ≫ a) (s ≫ b) (by rw [Category.assoc, h, Category.assoc])).choose_spec
      (gMatNat B s a b _ (gMatExists B a b h).choose_spec)
  · intro V a b k h h'
    apply Units.ext
    exact gMatUnique B a k _ _
      (gMatComp B a b k _ _ h (gMatExists B a b h).choose_spec (gMatExists B b k h').choose_spec)
      (gMatExists B a k (h.trans h')).choose_spec
  · intro V a b h
    exact (gMatExists B a b h).choose_spec
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaSection

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaSection :
    ∀ {σ : Type} (X : σ → Scheme.{0}) (f : ∀ p, Γ(X p, ⊤)), ∃ s : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s = f p) ∧ ∀ s' : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s' = f p) → s' = s := by
  intro σ X f
  let L := isLimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) (coproductIsCoproduct X).op
  let e : Γ(∐ X, ⊤) ≃ ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    Types.isLimitEquivSections L
  have hproj : ∀ (s : Γ(∐ X, ⊤)) (p : σ), (e s).val (Opposite.op ⟨p⟩) = (Sigma.ι X p).appTop.hom s :=
    fun s p => Types.isLimitEquivSections_apply L (Opposite.op ⟨p⟩) s
  let sec : ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    ⟨fun j => f j.unop.as, by
      rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨h⟩⟩
      cases h
      rfl⟩
  refine ⟨e.symm sec, fun p => ?_, fun s' hs' => e.injective ?_⟩
  · rw [← hproj, Equiv.apply_symm_apply]
  · apply Subtype.ext
    funext j
    obtain ⟨⟨q⟩⟩ := j
    rw [hproj, hs', Equiv.apply_symm_apply]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsV

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsV :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y), ∃ v : Fin d → Γ(TP B j, ⊤), IsV B j v ∧ Ideal.span (Set.range v) = ⊤ := by
  intro K _ W Z Y q i π D d B T j
  classical
  let X : B.ι × Fin d → Scheme.{0} := fun p => (oT B j p : Scheme.{0})
  choose v hv _ using fun m : Fin d =>
    sigmaSection X (fun p => uV B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) m)
  refine ⟨v, fun p m => hv m p, ?_⟩
  choose b hb _ using fun m : Fin d =>
    sigmaSection X (fun p => if p.2 = m then (1 : Γ(X p, ⊤)) else 0)
  obtain ⟨s, -, hs⟩ := sigmaSection X (fun _ => 1)
  have h1 : (∑ m, b m * v m) = 1 := by
    have e2 := hs 1 (fun p => map_one _)
    have e1 : (∑ m, b m * v m) = s := by
      refine hs _ fun p => ?_

      rw [map_sum]
      simp only [map_mul, hb, hv]
      simp [uSelf]
    rw [e1, e2]
  rw [Ideal.eq_top_iff_one, ← h1]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TCover

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.tCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → Smooth (eP B j) ∧ Surjective (eP B j) := by
  intro K _ W Z Y q i π D d B T j r hsq
  refine ⟨?_, ?_⟩
  · have hloc : IsZariskiLocalAtSource @Smooth.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    unfold eP
    exact IsZariskiLocalAtSource.sigmaDesc fun p => inferInstance
  · refine ⟨fun x => ?_⟩
    have hx : r x ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (Set.mem_univ (r x))
    have hx' : i (r x) ∈ (⨆ α, B.V α) := hx
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    have h3 : π (j x) = i (r x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq.w]
    have h4 : j x ∈ π ⁻¹ᵁ B.V α := by
      change π (j x) ∈ B.V α
      rw [h3]; exact hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp ((B.c α).C_cover h4)
    let p : B.ι × Fin d := (α, k)
    have hp : x ∈ oT B j p := hk
    let y : (oT B j p : Scheme.{0}) := ⟨x, hp⟩
    have hc : tI B j p ≫ eP B j = (oT B j p).ι := by
      unfold tI eP
      exact Sigma.ι_desc _ _
    refine ⟨tI B j p y, ?_⟩
    have hy : (tI B j p ≫ eP B j) y = x := by
      rw [hc]
      rfl
    rw [← Scheme.Hom.comp_apply]
    exact hy
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.WCover

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.wCover :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d), Smooth (cP B) ∧ Surjective (cP B) := by
  intro K _ W Z Y q i π D d B
  refine ⟨?_, ⟨fun x => ?_⟩⟩
  · have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
    unfold cP
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun α => inferInstance)
  · have hx : i x ∈ ⨆ α, B.V α := B.cover (Set.mem_univ x)
    obtain ⟨α, hα⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
    obtain ⟨y, hy⟩ : x ∈ Set.range (oW B α).ι := by
      rw [Scheme.Opens.range_ι]
      exact hα
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    refine ⟨wI B α y, ?_⟩
    rw [← Scheme.Hom.comp_apply, h, hy]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PBEx

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.pBEx : UpperTheory.Gal.KunnethLefschetz.G.PBEx := by
  intro K _ W Z Y T q i π D d hB j r hsq
  obtain ⟨B⟩ := hB
  obtain ⟨g, gn, gc, gs⟩ := existsG B
  obtain ⟨v, hv, hu⟩ := existsV B j
  obtain ⟨sc, uc⟩ := wCover B
  obtain ⟨se, ue⟩ := tCover B j r hsq
  obtain ⟨cm, ct⟩ := coverComm B j r hsq.w
  have hτ : ∀ {V : Scheme.{0}} (a b : V ⟶ TP B j), a ≫ eP B j = b ≫ eP B j →
      (a ≫ tauP B j) ≫ D.f = (b ≫ tauP B j) ≫ D.f := fun a b h => by
    rw [Category.assoc, Category.assoc, ct, reassoc_of% h]
  have hone : ∀ {V : Scheme.{0}} (a b : V ⟶ WP B) (e : a = b) (h : a ≫ cP B = b ≫ cP B), g a b h = 1 := by
    intro V a b e h
    subst e
    have := gc a a a h h
    exact mul_eq_left.1 this
  let P : PBData r d :=
    { W' := WP B
      c := cP B
      g := g
      g_nat := gn
      g_coc := gc
      T' := TP B j
      e := eP B j
      ρ := rhoP B j r hsq.w
      comm := cm
      v := fun a => ⟨a.appTop.hom ∘ v, by
        rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]⟩
      v_nat := fun s a => by
        funext m
        simp only [Function.comp_apply, Scheme.Hom.comp_appTop]
        rfl
      w := fun a b h => (D.u _ _ (hτ a b h))⁻¹
      gv := fun a b h h' => gvField B j r hsq v hv a b h (hτ a b h) _ (gs _ _ h')
      inj := fun a b h' u hh => injField B j r hsq v hv a b _ h' (gs _ _ h') u hh
      onto := fun a₀ v₀ x => by
        obtain ⟨U, a, u, hx, ha, hv'⟩ := ontoField B j r hsq v hv a₀ v₀ x
        have h : (a ≫ rhoP B j r hsq.w) ≫ cP B = (U.ι ≫ a₀) ≫ cP B := by rw [ha]
        refine ⟨U, a, h, u, hx, ?_⟩
        rw [hone _ _ ha h]
        simpa using hv' }
  exact ⟨P, tauP B j, ct, fun a b h h' => rfl⟩
end
end
