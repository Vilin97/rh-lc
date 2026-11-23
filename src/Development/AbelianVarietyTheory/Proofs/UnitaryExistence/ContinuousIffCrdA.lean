module

public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ConjugateFieldNorm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct

section Adelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]

def cjF : E →ₐ[F] E :=
  { (IsCMField.complexConj E : E →+* E) with
    commutes' := fun x => by
      have h : algebraMap F E x ∈ maximalRealSubfield E := by
        rw [mem_maximalRealSubfield_iff]
        intro φ
        exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))) x
      exact (IsCMField.complexConj E).commutes ⟨_, h⟩ }

abbrev Af : Type := FiniteAdeleRing (𝓞 F) F

abbrev Ai : Type := InfiniteAdeleRing F

structure HSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) where
  Gm : Matrix (Fin r) (Fin r) E
  Gm_herm : ∀ a b, cc (Gm a b) = Gm b a
  Gm_det : Gm.det ≠ 0
  L : Submodule (𝓞 E) (Fin r → E)
  L_fg : L.FG
  L_span : Submodule.span E (L : Set (Fin r → E)) = ⊤
  L_dual : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gm x y)

def HSpace.std (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) : HSpace E r where
  Gm := 1
  Gm_herm a b := by by_cases h : a = b <;> simp [cc, Matrix.one_apply, h, eq_comm]
  Gm_det := by simp
  L := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
  L_fg := Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  L_span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (x i) : Fin r → E) = x i • (Pi.single i 1 : Fin r → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span fun k _ => ?_)
    by_cases h : k = i
    · subst h; simpa using Submodule.one_le.1 le_rfl
    · simp [h]
  L_dual x := by
    have hi : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z => by
      rw [Submodule.mem_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
    have hh : ∀ y, herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := fun y => by
      simp [herm, Matrix.one_apply]
    constructor
    · intro hx y hy
      rw [hh]
      refine IsIntegral.sum _ fun a _ => ((hi _).1 (hx a trivial)).mul ?_
      exact ((hi _).1 (hy a trivial)).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
    · intro h a _
      have := h (Pi.single a 1) fun k _ => by
        by_cases hk : k = a
        · subst hk; simpa using Submodule.one_le.1 le_rfl
        · simp [hk]
      rw [hh, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc]) (by simp)] at this
      exact (hi _).2 (by simpa [cc] using this)

variable {r : ℕ}

variable (A : Type) [CommRing A] [Algebra F A]

def incl : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom

def hermA (V : HSpace E r) (x y : Fin r → A ⊗[F] E) : A ⊗[F] E :=
  ∑ a, ∑ b, x a * incl F A (V.Gm a b) * Algebra.TensorProduct.map (AlgHom.id F A) (cjF F) (y b)

def UA (V : HSpace E r) : Subgroup (GL (Fin r) (A ⊗[F] E)) where
  carrier := {g | ∀ x y, hermA F A V (g.val.mulVec x) (g.val.mulVec y) = hermA F A V x y}
  one_mem' := fun x y => by simp
  mul_mem' := fun {g h} hg hh x y => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg x y => by
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec]

abbrev GA (V : HSpace E r) : Type := UA F (Ai F) V × UA F (Af F) V

def IsRat (V : HSpace E r) (γ : GL (Fin r) E) (g : GA F V) : Prop :=
  g.1.1.val = γ.val.map (incl F (Ai F)) ∧ g.2.1.val = γ.val.map (incl F (Af F))

def latHat (L : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → Af F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ L, z = fun i => a ⊗ₜ[F] x i}

def levelK (V : HSpace E r) (N : ℕ) : Subgroup (GA F V) where
  carrier := {k | k.1 = 1 ∧ (∀ z, z ∈ latHat F V.L ↔ k.2.1.val.mulVec z ∈ latHat F V.L) ∧
    ∀ z ∈ latHat F V.L, ∃ w ∈ latHat F V.L, k.2.1.val.mulVec z - z = N • w}
  one_mem' := ⟨rfl, fun z => by simp, fun z _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have e : ∀ z, (g * h).2.1.val.mulVec z = g.2.1.val.mulVec (h.2.1.val.mulVec z) := fun z => by
      rw [Matrix.mulVec_mulVec]; rfl
    refine ⟨by rw [Prod.fst_mul, g1, h1, mul_one], fun z => by rw [e, ← g2, ← h2], fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := h3 z hz
    obtain ⟨w', hw', e2⟩ := g3 _ ((h2 z).1 hz)
    exact ⟨w' + w, add_mem hw' hw, by rw [e, smul_add, ← e1, ← e2]; abel⟩
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have e : ∀ z, g.2.1.val.mulVec ((g⁻¹).2.1.val.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec]
      have : g.2.1.val * (g⁻¹).2.1.val = 1 := Units.mul_inv _
      rw [this, Matrix.one_mulVec]
    have s : ∀ z, z ∈ latHat F V.L ↔ (g⁻¹).2.1.val.mulVec z ∈ latHat F V.L := fun z => by
      rw [g2 ((g⁻¹).2.1.val.mulVec z), e]
    refine ⟨by rw [Prod.fst_inv, g1, inv_one], s, fun z hz => ?_⟩
    obtain ⟨w, hw, e1⟩ := g3 _ ((s z).1 hz)
    exact ⟨-w, neg_mem hw, by rw [smul_neg, ← e1, e]; abel⟩

def latAt (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (V : HSpace E r) (g : UA F (Af F) V) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : Fin r → E,
    (∃ z ∈ latHat F V.L, (fun i => incl F (Af F) (x i)) = g.1.val.mulVec z) ∧ v = a • x}

end Adelic

structure Nums (E : Type) [Field E] [NumberField E] where
  k : ℕ
  m : ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  Nc : ℕ
  Nc_pos : 0 < Nc
  AA : FractionalIdeal (nonZeroDivisors (𝓞 E)) E
  Os : Subring ℂ

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Nums.r (R : Nums E) : ℕ := R.k + R.m - 1

abbrev Nums.J (R : Nums E) : Type := {j : ℕ // 1 ≤ j ∧ j ≤ R.m}

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E]

structure CorePar (R : Nums E) : Type 1 where
  H : Host E
  l : Level H
  c : Coeff l
  Dw : R.J → Datum H
  Xo : ∀ j, Moduli (Dw j) l

  U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ R.r

  V : R.J → HSpace E R.r

  dict : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → Σ k, Frame ((U j σ).X k).Ψ R.r

  mu : ∀ j (σ : c.F →+* ℂ), GoodEmb c σ → GA F (V j) → ℂ

  Kf : ∀ j, Subgroup (GA F (V j))

  pi : Fin 2 → 𝓞 E

namespace CorePar

variable {F} {R : Nums E} (Q : CorePar F R)

end CorePar

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
end
end
end

-- Source module: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspFormLaws

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldNorm
open scoped TensorProduct

section Quot

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

@[reducible] def topU (A : Type) [CommRing A] [Algebra F A] [t : TopologicalSpace A] (V : HSpace E r) :
    TopologicalSpace (UA F A V) :=
  ⨅ (a : Fin r) (b : Fin r) (φ : E →ₗ[F] F),
    t.induced fun g => TensorProduct.rid F A (LinearMap.lTensor A φ (g.1.val a b))

@[reducible] def topG (V : HSpace E r) : TopologicalSpace (GA F V) :=
  (topU F (Ai F) V).induced Prod.fst ⊓ (topU F (Af F) V).induced Prod.snd

def ratG (V : HSpace E r) : Subgroup (GA F V) where
  carrier := {g | ∃ γ, IsRat F V γ g}
  one_mem' := ⟨1, by simp [IsRat, Matrix.map_one]⟩
  mul_mem' := by
    rintro g h ⟨γ, g1, g2⟩ ⟨δ, h1, h2⟩
    refine ⟨γ * δ, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.map_mul, ← g1, ← h1]; rfl
    · rw [Units.val_mul, Matrix.map_mul, ← g2, ← h2]; rfl
  inv_mem' := by
    rintro g ⟨γ, g1, g2⟩
    have e1 : g.1.1 = Matrix.GeneralLinearGroup.map (incl F (Ai F)) γ := Units.ext g1
    have e2 : g.2.1 = Matrix.GeneralLinearGroup.map (incl F (Af F)) γ := Units.ext g2
    refine ⟨γ⁻¹, ?_, ?_⟩
    · change (g.1.1⁻¹).val = _
      rw [e1, ← map_inv]; rfl
    · change (g.2.1⁻¹).val = _
      rw [e2, ← map_inv]; rfl

def AutQ (V : HSpace E r) : Type := Quotient (QuotientGroup.rightRel (ratG F V))

def autMk (V : HSpace E r) (g : GA F V) : AutQ F V := Quotient.mk _ g

instance (V : HSpace E r) : MeasurableSpace (AutQ F V) := (@borel _ (topG F V)).map (autMk F V)

def autRt (V : HSpace E r) (h : GA F V) : AutQ F V → AutQ F V :=
  Quotient.map' (· * h) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab

def IsAutProb (V : HSpace E r) (ν : Measure (AutQ F V)) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ h s, MeasurableSet s → ν (autRt F V h ⁻¹' s) = ν s

def FinVol (V : HSpace E r) : Prop := ∃ ν, IsAutProb F V ν

end Quot

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [Algebra F E] {R : Nums E} (Q : CorePar F R)

variable {Q}

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphismGroupTopologies
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)




end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

def crdR : V.V ≃ₗ[D.host.E] (Fin r → D.host.E) := (V.frame.reindex (finCongr hr)).equivFun

def gramR : Matrix (Fin r) (Fin r) D.host.E := (Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ

theorem herm_crdR (x y : V.V) : herm (gramR V hr) (crdR V hr x) (crdR V hr y) = V.hT y x := by
  subst hr
  rw [Formalism.L2.Herm.hT_crd D.sp.cm V]
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [crdR, gramR, finCongr_refl, Matrix.reindex_refl_refl, Module.Basis.reindex_refl]
  change _ * V.gram b a * cc _ = cc _ * V.gram b a * _
  unfold Formalism.L2.Herm.crd
  ring

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩

def spOf : ConjugateFieldNorm.HSpace D.host.E r where
  Gm := gramR V hr
  Gm_herm a b := V.herm.eq _ _
  Gm_det h := by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    refine hv ((congrArg _ (V.nondeg.2 x fun y => ?_)).trans (map_zero _))
    rw [← herm_crdR V hr, herm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, show ∑ a, crdR V hr x a * gramR V hr a b = 0 from congrFun h0 b, zero_mul]
  L := V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E))
  L_fg := V.standardTuple_isLattice.fg.map _
  L_span := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      by_contra hproper
      obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hproper)
      have hinj : Function.Injective V.hT := LinearMap.ker_eq_bot.mp
        (LinearMap.separatingLeft_iff_ker_eq_bot.mp V.nondeg.1)
      let e := LinearEquiv.ofInjective V.hT hinj
      have hrank : Module.rank D.host.E V.V = Module.rank D.host.E (LinearMap.range V.hT) :=
        rank_eq_of_equiv_equiv (starRingEnd D.host.E) e.toAddEquiv
          (star_involutive.bijective) (map_smulₛₗ e)
      have hsurj : Function.Surjective V.hT := by
        rw [← LinearMap.range_eq_top]
        apply Submodule.eq_top_of_finrank_eq
        change Module.finrank D.host.E (LinearMap.range V.hT) =
          Module.finrank D.host.E (Module.Dual D.host.E V.V)
        rw [Subspace.dual_finrank_eq]
        exact congrArg Cardinal.toNat hrank.symm
      obtain ⟨x, hx⟩ := hsurj φ
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hφ (hx.symm.trans V.hT.map_zero)
      have hline (c : D.host.E) : c • x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hxy : V.hT x y = 0 := by
          rw [hx]
          exact hker (Submodule.subset_span hy)
        rw [LinearMap.restrictScalars_apply, map_smul, V.herm.eq_iff.mp hxy, smul_zero]
        exact Submodule.zero_mem _
      obtain ⟨y, hy⟩ : ∃ y, V.hT y x ≠ 0 := by
        simpa only [not_forall, not_not] using mt (V.nondeg.2 x) hx0
      let f := ((V.hT y).restrictScalars (𝓞 D.host.E)).comp V.L0.subtype
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_surjective f <| by
        intro z
        refine ⟨⟨(z / V.hT y x) • x, hline _⟩, ?_⟩
        change V.hT y ((z / V.hT y x) • x) = z
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField RingOfIntegers.coe_injective (Field.toIsField _))
    rw [Submodule.map_coe]
    change Submodule.span D.host.E ((crdR V hr).toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  L_dual v := by
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    have h1 : crdR V hr x ∈ V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E)) ↔ x ∈ V.L0 :=
      ⟨fun ⟨y, hy, e⟩ => (crdR V hr).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, IsIntegral ℤ (V.hT y x) := by
      conv_lhs => rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_one_iff]
      rfl
    rw [h1, h2]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact (herm_crdR V hr x y).symm ▸ h y hy
    · intro h y hy
      exact herm_crdR V hr x y ▸ h _ ⟨y, hy, rfl⟩

structure IsCoord (V' : ConjugateFieldNorm.HSpace D.host.E r) (ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V) : Prop where
  sp : V' = spOf V hr
  inf : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (infHom V (ψ g)).val = g.1.1.val
  fin : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (finHom V (ψ g)).val = g.2.1.val
  top : AutomorphismGroupTopologies.topG D.host.F V' = TopologicalSpace.induced ψ inferInstance

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

def IsCoord.quotEquiv (h : IsCoord V hr V' ψ) : AutomorphismGroupTopologies.AutQ D.host.F V' ≃ᵐ Formalism.L2.Pj.AutQ V where
  toEquiv := Quotient.congr ψ.toEquiv fun a b => by
    have mem_GQ (g : ConjugateFieldNorm.GA D.host.F V') :
        ψ g ∈ GQ V ↔ g ∈ AutomorphismGroupTopologies.ratG D.host.F V' := by
      subst hr
      let p := (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      let q := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
      have hInf : (matHom V (ψ g)).val.map p = g.1.1.val := h.inf g
      have hFin : (matHom V (ψ g)).val.map q = g.2.1.val := h.fin g
      constructor
      · rintro ⟨γ, -, e⟩
        have he : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) :=
          (congrArg Units.val e).symm
        refine ⟨γ, ?_, ?_⟩
        · rw [← hInf, he]
          ext i j
          simp [p, inclR, ConjugateFieldNorm.incl]
        · rw [← hFin, he]
          ext i j
          simp [q, inclR, ConjugateFieldNorm.incl]
      · rintro ⟨γ, eInf, eFin⟩
        obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
        have he' : (matHom V (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := by
          ext i j
          refine e.injective (Prod.ext ?_ ?_)
          · rw [(he _).1, (he _).1]
            exact congrFun (congrFun (hInf.trans eInf) i) j
          · rw [(he _).2, (he _).2]
            exact congrFun (congrFun (hFin.trans eFin) i) j
        refine ⟨γ, ?_, Units.ext he'.symm⟩
        have hu : Formalism.UG.cT (sigR _ D.sp.cm.sig) (matHom V (ψ g)).val *
            JR _ V.gram * (matHom V (ψ g)).val = JR _ V.gram := (ψ g).2
        have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
          Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
        change Formalism.UG.cT _ γ.val * V.gram * γ.val = V.gram
        refine Matrix.map_injective hinj ?_
        change (_ : Matrix _ _ _).map _ = JR _ V.gram
        rw [← hu, he', Matrix.map_mul, Matrix.map_mul]
        congr 2
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change _ ↔ ψ b * (ψ a)⁻¹ ∈ GQ V
    rw [← map_inv, ← map_mul]
    exact (mem_GQ _).symm
  measurable_toFun s hs := by
    change MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (ψ ⁻¹' (Formalism.L2.Pj.autMk V ⁻¹' s))
    rw [h.top, borel_comap]
    exact ⟨_, hs, rfl⟩
  measurable_invFun s hs := by
    have hs' : MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s) := hs
    rw [h.top, borel_comap] at hs'
    obtain ⟨t, ht, e⟩ := hs'
    change MeasurableSet (ψ.symm ⁻¹' (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s))
    rw [← e, ← Set.preimage_comp]
    simpa using ht

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

end Rec

end GlobalTheory.CoreLawsCompare
end
end
end
