module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Aesop.Main
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.AmMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CokerBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ContOfKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DualBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExactMid
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExistsCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.GenTrick
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H0LocalCardBoundedOfClsKerLeKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ImgCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.MapConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdHalf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdSESInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Transl
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Basify

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdCount

section

@[expose] public section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odCount :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X] (D : Dat x.A (plOf G)) (d : ℕ) (dv : L.Vl → ℕ), l ≠ 2 → IsOd h x X D → CohAx G d dv → Finite D.H2LocalConditions ∧ Finite D.Ck2 ∧ Nat.card D.H2LocalConditions ≤ Nat.card D.Sel * (∏ v, Nat.card (H0 (D.Q (inV G v)).ρ)) * Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  intro l _ L G G0 h n x X _ _ _ D d dv hl hD hC
  obtain ⟨hM, hfixc, hQv⟩ := odHalf l L G G0 h n x X D hl hD
  obtain ⟨ktM, ktQ, ktJ⟩ := odKill l L G G0 h n x X D hD
  set N := Nat.card X ^ (x.a * (n - x.a)) with hN
  have hNpos : 0 < N := pow_pos Nat.card_pos _
  have fM := hC.fin x.A D.M ktM
  have fQ : ∀ w, Finite (H1 (D.Q w).ρ) ∧ Finite (H2 (D.Q w).ρ) := by
    intro w
    cases w with
    | inl v => exact hC.finV v x.A (D.Q (inV G v)) (ktQ _)
    | inr u => exact hC.finU u x.A (D.Q (inU G u)) (ktQ _)
  let dw : (plOf G).ι → ℕ := Sum.elim dv (fun _ => 0)
  let e : (plOf G).ι → ℕ := Sum.elim (fun v => Nat.card (H0 (D.Q (inV G v)).ρ)) (fun _ => 1)
  have hglob : Nat.card (H2 D.M.ρ) * N ^ ∑ w, dw w ≤ Nat.card (H1 D.M.ρ) := by
    obtain ⟨c, hc, hE⟩ := hC.ge
    have E := hE x.A D.M ktM
    have hfix : ∀ i, Nat.card {m // D.M.ρ (c i) m = m} = N := fun i => hfixc (c i) (hc i).1 (hc i).2
    simp only [hfix, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hM] at E
    have hsum : ∑ w, dw w = d := by
      show ∑ w : L.Vl ⊕ L.St, dw w = d
      rw [Fintype.sum_sum_type]
      simp [dw, hC.sum]
    rw [hsum]
    have h0pos : 0 < Nat.card (H0 D.M.ρ) := Nat.card_pos
    have key : Nat.card (H0 D.M.ρ) * Nat.card (H2 D.M.ρ) * N ^ d = Nat.card (H1 D.M.ρ) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hNpos d)
      rw [← E]
      ring
    calc Nat.card (H2 D.M.ρ) * N ^ d ≤ Nat.card (H0 D.M.ρ) * (Nat.card (H2 D.M.ρ) * N ^ d) :=
          Nat.le_mul_of_pos_left _ h0pos
      _ = Nat.card (H1 D.M.ρ) := by rw [← key, mul_assoc]
  have hloc : ∀ w, Nat.card (H1 (D.Q w).ρ) ≤
      Nat.card (H1ur (D.Q w).ρ ((plOf G).J w)) * Nat.card (H2 (D.Q w).ρ) * e w * N ^ dw w := by
    intro w
    cases w with
    | inl v =>
      have E := hC.leV v x.A (D.Q (inV G v)) (ktQ _)
      rw [hQv v] at E
      haveI := (fQ (inV G v)).1
      have hur : 0 < Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) := Nat.card_pos
      have key : Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v
          ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
            Nat.card (H2 (D.Q (inV G v)).ρ) * Nat.card (H0 (D.Q (inV G v)).ρ) * N ^ dv v := by
        calc _ ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
              (Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v) :=
              Nat.le_mul_of_pos_left _ hur
          _ = _ := by ring
      exact E.le.trans key
    | inr u =>
      have E := hC.leU u x.A (D.Q (inU G u)) (ktQ _)
      have ur := ((hC.ur u) x.A (D.Q (inU G u)) (ktQ _) (ktJ u)).1
      rw [pow_zero, mul_one] at E
      have key : Nat.card (H0 (D.Q (inU G u)).ρ) * Nat.card (H2 (D.Q (inU G u)).ρ)
          ≤ Nat.card (H1ur (D.Q (inU G u)).ρ (L.Ju u)) * Nat.card (H2 (D.Q (inU G u)).ρ) * 1 * N ^ 0 := by
        rw [pow_zero, mul_one, mul_one]
        exact Nat.mul_le_mul_right _ ur
      exact E.le.trans key
  obtain ⟨hfin, hle⟩ := count x.A G.Γ (plOf G) D N dw e hNpos fM.1 fM.2 fQ hglob hloc
  have hfin2 : Finite D.Ck2 := by
    haveI : Fintype (plOf G).ι := (plOf G).fin
    haveI : ∀ w, Finite (H2 (D.Q w).ρ) := fun w => (fQ w).2
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨hfin, hfin2, ?_⟩
  have hck := hC.ck x.A D ktM
  have hprod : ∏ w, e w = ∏ v, Nat.card (H0 (D.Q (inV G v)).ρ) := by
    show ∏ w : L.Vl ⊕ L.St, e w = _
    rw [Fintype.prod_sum_type]
    simp [e]
  calc Nat.card D.H2LocalConditions ≤ (Nat.card D.Sel * ∏ w, e w) * Nat.card D.Ck2 := hle
    _ ≤ _ := by rw [hprod]; exact Nat.mul_le_mul_left _ hck
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdLam

section

@[expose] public section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundOfDuality

section

@[expose] public section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W IsLocalRing

namespace UpperTheory.V.Pa.B2

private theorem h2_comp_eq_smul_of_comp_eq_smul {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} {D D' : Dat A P}
    (r : D.Hom D') (f : D'.Hom D) (a : A) (h : ∀ m, f.f (r.f m) = a • m) (y : D.H2LocalConditions) : f.h2 (r.h2 y) = a • y := by
  have hq : ∀ w (q : (D.Q w).X), f.fq w (r.fq w q) = a • q := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [r.comm, f.comm, h, map_smul]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Dat.Hom.h2, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  simp only [LinearMap.restrict_apply, Submodule.coe_smul]
  refine Prod.ext ?_ ?_
  · funext s
    exact h _
  · funext w g
    exact hq w _

private theorem smul_H2_local_eq_zero_of_smul_eq_zero {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (a : A) (h : ∀ m : D.M.X, a • m = 0) (y : D.H2LocalConditions) : a • y = 0 := by
  have hq : ∀ w (q : (D.Q w).X), a • q = 0 := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [← map_smul, h, map_zero]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul]
  have hz : a • z = 0 := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · funext s
      exact h _
    · funext w g
      exact hq w _
  rw [hz, Submodule.Quotient.mk_zero]

private theorem finAm (K : Type) [Field K] [Finite K] (m : ℕ) :
    Finite (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) := by
  classical
  let g : (Fin m → K) → PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} :=
    fun c => Ideal.Quotient.mk _ (∑ i : Fin m, c i • (PowerSeries.X : PowerSeries K) ^ (i : ℕ))
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => PowerSeries.coeff (i : ℕ) f, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro n hn

  rw [map_sub, map_sum]
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Fin.ext e.symm)
  · simp

section
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}

private theorem smul_eq_zero_of_algebraMap_eq_zero_of_isOd {X : Type} [CommRing X] [Algebra x.A X] {D : Dat x.A (plOf G)} (o : IsOd h x X D) (a : x.A)
    (ha : algebraMap x.A X a = 0) (y : D.M.X) : a • y = 0 := by
  apply o.e.injective
  rw [map_smul, map_zero]
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_zero, ← algebraMap_smul X a, ha, zero_smul]


private theorem step {X X' X'' : Type} [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] [CommRing X'']
    [Algebra x.A X''] {D D' D'' : Dat x.A (plOf G)} (o : IsOd h x X D) (o' : IsOd h x X' D') (o'' : IsOd h x X'' D'')
    {d : ℕ} {dv : L.Vl → ℕ} (hA : CohAx G d dv) (a : x.A) [Finite D''.H2LocalConditions] (hF : Finite D''.Ck2)
    (uf : X' →ₗ[x.A] X) (ug : X →ₗ[x.A] X'') (uk : X'' →ₗ[x.A] X) (ur : X →ₗ[x.A] X')
    (i1 : Function.Injective uf) (i2 : Function.Exact uf ug) (i3 : Function.Surjective ug) (i4 : Function.Injective uk)
    (i5 : Function.Exact uk ur) (i6 : Function.Surjective ur) (i7 : ∀ y, uf (ur y) = a • y) :
    Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a)) ≤ Nat.card D''.H2LocalConditions * Nat.card D''.Ck2 := by
  obtain ⟨f1, hf1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o' o uf
  obtain ⟨g1, hg1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o'' ug
  obtain ⟨k1, hk1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o'' o uk
  obtain ⟨r1, hr1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o' ur
  have s1 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o' o o'' uf ug f1 g1 hf1 hg1 i1 i2 i3
  have s2 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o'' o o' uk ur k1 r1 hk1 hr1 i4 i5 i6
  have hcomp : ∀ m, f1.f (r1.f m) = a • m := by
    intro m
    apply o.e.injective
    apply Subtype.ext
    rw [hf1, hr1, Matrix.map_map, map_smul, Submodule.coe_smul]
    ext i j
    simp [i7]
  have hex : g1.h2.ker ≤ f1.h2.range :=
    exactMid _ _ _ _ _ _ f1 g1 s1 (odLam _ _ _ _ h _ x _ _ _ _ o o'' g1 s1.surj hA.ur)
  have hon : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r1.f (by continuity) r1.equiv) :=
    hA.onto _ D.M D'.M (odKill _ _ _ _ h _ x _ _ o).1 r1.f r1.equiv s2.surj
  obtain ⟨hfin, hcard⟩ := cokerBound _ _ _ _ _ _ k1 r1 s2 hon hF
  have hfr : ∀ y, f1.h2 (r1.h2 y) = a • y := h2_comp_eq_smul_of_comp_eq_smul r1 f1 a hcomp
  set R := LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a) with hRdef
  have hRF : R ≤ LinearMap.range f1.h2 := by
    rintro _ ⟨y, rfl⟩
    exact ⟨r1.h2 y, by rw [hfr]; rfl⟩
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range f1.h2) R hRF, mul_comm]
  apply Nat.mul_le_mul
  · have hfk : Finite (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
      Finite.of_equiv _ (LinearMap.quotKerEquivRange g1.h2).toEquiv.symm
    have hs : Function.Surjective ((LinearMap.ker g1.h2).liftQ (LinearMap.range f1.h2).mkQ
        (by rw [Submodule.ker_mkQ]; exact hex)) := by
      intro q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    calc Nat.card (D.H2LocalConditions ⧸ LinearMap.range f1.h2) ≤ Nat.card (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
          Nat.card_le_card_of_surjective _ hs
      _ = Nat.card (LinearMap.range g1.h2) := Nat.card_congr (LinearMap.quotKerEquivRange g1.h2).toEquiv
      _ ≤ Nat.card D''.H2LocalConditions := Nat.card_le_card_of_injective _ Subtype.val_injective
  · have hker : LinearMap.range r1.h2 ≤ LinearMap.ker (R.mkQ ∘ₗ f1.h2) := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hfr]
      exact ⟨y, rfl⟩
    have hmap : (LinearMap.range f1.h2).map R.mkQ = LinearMap.range ((LinearMap.range r1.h2).liftQ _ hker) := by
      rw [Submodule.range_liftQ, LinearMap.range_comp]
    rw [hmap]
    refine le_trans ?_ hcard
    exact Nat.card_le_card_of_surjective _ (LinearMap.surjective_rangeRestrict _)

end


theorem obstructionBound_of_duality : ObstructionBoundFromDuality := by
  intro l _ L G0 T n x k al d hl h0 hN hH hE
  obtain ⟨dv0, hA0⟩ := h0
  obtain ⟨C0, hC0⟩ := sel0 l L G0 n x k d dv0 hl hA0
  obtain ⟨Cn, hCn⟩ := selN l L G0 T n x al hH hE
  obtain ⟨Ch, hCh⟩ := H0_local_card_bounded_of_cls_ker_le_ker l L G0 n x
  obtain ⟨Cd, hCd⟩ := dualBound l L G0 n x
  have hres : Nat.card (ResidueField x.A) = Nat.card x.K :=
    Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv
  haveI : Finite (ResidueField x.A) := Finite.of_equiv _ PowerSeries.residueFieldOfPowerSeries.toEquiv.symm
  have hzero : ∀ e, algebraMap x.A (x.Am e) (x.t ^ e) = 0 := fun e =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  haveI : ∀ e, Finite (x.Am e) := fun e => finAm x.K e
  refine ⟨C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd, fun m => ?_⟩
  filter_upwards [hCn m] with N hNm
  intro z hz
  obtain ⟨dvN, hAN⟩ := hN N
  obtain ⟨D, ⟨o⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am m) ⟨m, hzero m⟩
  obtain ⟨ξ, hξ⟩ := transl l L (T.GN N) G0 (T.h N) n x k (x.Am m) D (k.g + 1) z hl ⟨m, hzero m⟩ o hAN.ur hz
  haveI : Finite D.H2LocalConditions := (odCount l L (T.GN N) G0 (T.h N) n x (x.Am m) D d dvN hl o hAN).1
  have hbound : ∀ e ≤ m, Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions (x.t ^ e))) ≤
      Nat.card (ResidueField x.A) ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
    intro e he
    rw [hres]
    obtain ⟨uf, ug, uk, ur, i1, i2, i3, i4, i5, i6, i7⟩ := amMaps x.K e m he
    obtain ⟨D1, ⟨o1⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am (m - e)) ⟨m - e, hzero (m - e)⟩
    obtain ⟨D2, ⟨o2⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨D0, ⟨o0⟩⟩ := odEx l L G0 G0 (Glob.Hom.refl G0) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨hf2, hc2, hcnt⟩ := odCount l L (T.GN N) G0 (T.h N) n x (x.Am e) D2 d dvN hl o2 hAN
    haveI := hf2
    have hs := step o o1 o2 hAN (x.t ^ e) hc2 uf ug uk ur i1 i2 i3 i4 i5 i6 i7
    have hck := hAN.ck _ D2 (odKill _ _ _ _ _ _ x _ _ o2).1
    have hsel := hNm e he D2 D0 o2 o0 (hA0.fin _ D0.M (odKill _ _ _ _ _ _ x _ _ o0).1).1
    have hs0 := hC0 e D0 o0
    have hprod : ∏ v, Nat.card (H0 (D2.Q (inV (T.GN N) v)).ρ) ≤ (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl := by
      rw [← Finset.card_univ]
      exact Finset.prod_le_pow_card _ _ _ (fun v _ => hCh (T.GN N) (T.h N) e D2 o2 v)
    have hd := hCd (T.GN N) (T.h N) e D2 o2
    calc _ ≤ Nat.card D2.H2LocalConditions * Nat.card D2.Ck2 := hs
      _ ≤ ((Nat.card x.K ^ (k.g * e + C0) * Nat.card x.K ^ Cn) * (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl
            * Nat.card x.K ^ Cd) * Nat.card x.K ^ Cd := by
          apply Nat.mul_le_mul
          · refine hcnt.trans ?_
            apply Nat.mul_le_mul _ hd
            apply Nat.mul_le_mul _ hprod
            exact hsel.trans (Nat.mul_le_mul_right _ hs0)
          · exact hck.trans hd
      _ = Nat.card x.K ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
          rw [← pow_mul]
          simp only [← pow_add]
          congr 1
          ring
  have hkill : ∀ y : D.H2LocalConditions, x.t ^ m • y = 0 := smul_H2_local_eq_zero_of_smul_eq_zero D _ (smul_eq_zero_of_algebraMap_eq_zero_of_isOd o _ (hzero m))
  obtain ⟨c, hcu, hc⟩ := genTrick x.A D.H2LocalConditions x.t k.g (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) m
    PowerSeries.X_irreducible hkill hbound (fun i => Submodule.Quotient.mk (ξ i))
  refine ⟨c, hcu, ?_⟩
  have hmem : ↑(∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) ∈ D.selmerSecondCoboundaries := by
    have hsum : (∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) =
        x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i := by
      rw [Finset.smul_sum]
      simp only [mul_smul]
    rw [hsum]
    simp only [← Submodule.Quotient.mk_smul] at hc
    have h1 : Submodule.Quotient.mk (p := Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)
        (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i) = 0 := by

      rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, map_sum]
      exact hc
    exact Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero (Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)).mp h1)
  obtain ⟨Ψ, hΨ, hΨe⟩ := hξ _ hmem
  refine ⟨Ψ, hΨ, fun j γ a b => ?_⟩
  rw [hΨe, Finset.smul_sum]
  simp only [mul_smul]

end UpperTheory.V.Pa.B2
end
end
