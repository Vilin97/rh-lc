module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAmpFramesExponents
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyZOnOfComponents

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

theorem _root_.GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.ModelOfOutput.exists_zOn | exact GlobalTheory.ModelOfOutput.exists_zOn | (intros; apply GlobalTheory.ModelOfOutput.exists_zOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenSetOfTTEqBot

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelTripleAmpleFramesComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelTripleAmpleFramesComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_model_triple_ampleFrames_component : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.exists_zon_ampFrames_component | exact GlobalTheory.exists_zon_ampFrames_component | (intros; apply GlobalTheory.exists_zon_ampFrames_component <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.nonempty_zOn_thetaFam : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  intro h1 h2 h3 h4 h5 h6 E _ _ _ H D n hpq hn hodd
  exact FamilyModel.nonempty_zOn_of_components GlobalTheory.T.exists_model_triple_ampleFrames_component h1 h2 h3 h4 h5 h6 E H D n hpq hn hodd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  first | exact @GlobalTheory.nonempty_zOn_thetaFam | exact GlobalTheory.nonempty_zOn_thetaFam | (intros; apply GlobalTheory.nonempty_zOn_thetaFam <;> assumption)
end
end
