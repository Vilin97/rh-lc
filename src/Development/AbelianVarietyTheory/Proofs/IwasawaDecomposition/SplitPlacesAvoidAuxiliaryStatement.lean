module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUnitOfNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.KerMemAbLocus
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDim
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Analysis.Normed.Algebra.GelfandRadius

-- Source module: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta

section

@[expose] public section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Dim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem generic_dim (A : DatAt Y P) : A.U.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have := A.t.semi.smooth
  have := A.t.semi.geomConnected
  have d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R)) := by
    have := A.U.A.smoothDim
    have : IsIso A.U.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))
    rw [show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]
    infer_instance
  have d₁ := GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀
  have e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have p₁ := (IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1
  have p₂ := (IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1
  rw [e] at p₁
  have d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁
  have d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ObjDim.smoothOfRelativeDimension Y.oF)
  have d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) := by
    rw [← p₁.isoIsPullback_hom_snd _ _ p₂]
    infer_instance
  have : Surjective A.t.G.hom := inferInstance
  obtain ⟨x, -⟩ := (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)
  simpa using H1.dim_unique _ d₂ d₄ x

theorem dim_add_rank (A : DatAt Y P) :
    A.U.D.toPre.P.g + Module.finrank ℤ A.Ylat = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G
    A.t.semi A.U.U
  rw [← generic_dim A, add_comm]
  exact h.symm

end Dim

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem finrank_host_eq (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem complexConj_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

def beLin : ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ := (ct.dat y).beLin (PointLawsEdge.betaAdd _ p)

def evidence : Per.Reading (ct.dat y) := (Per.nonempty_reading ct.hp.one_lt (ct.dat y)).some

def tauVal (a : ct.Ylat y) (χ : ct.chX y) : ((ct.fld y).C)ˣ := (ct.evidence y).t a ((ct.phi y).symm χ)

def lineShift (a : ct.Ylat y) : ct.chX y := ct.phi y a

def mulFst (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y a

def mulSnd (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y b

def mulConst (a b : ct.Ylat y) : ((ct.fld y).C)ˣ :=
  Exists.choose (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S))
    ⟨(ct.evidence y).t a b, (ct.evidence y).isVal a b⟩

def abDim : ℕ := (ct.dat y).U.D.toPre.P.g

theorem isTauVal_mulConst (a b : ct.Ylat y) :
    Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) ((ct.mulConst y a b : ((ct.fld y).C)ˣ) : (ct.fld y).C) :=
  Exists.choose_spec (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S)) _

theorem mulFst_eq (a b : ct.Ylat y) : ct.mulFst y a b = ct.phi y b := by
  rw [mulFst, lineShift, lineShift, map_add (f := _), add_sub_cancel_left]

theorem mulSnd_eq (a b : ct.Ylat y) : ct.mulSnd y a b = ct.phi y a := by
  rw [mulSnd, lineShift, lineShift, map_add (f := _), add_sub_cancel_right]

theorem mulConst_eq (a b : ct.Ylat y) : ct.mulConst y a b = ct.tauVal y a (ct.phi y b) :=
  Units.ext ((ct.evidence y).eq_of_isTauVal (ct.isTauVal_mulConst y a b))

theorem abDim_add : ct.abDim y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N := by
  have h := dim_add_rank (ct.dat y)
  rw [finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos] at h
  exact h

end At

def motTrue (ct : At S κ p) : MotSt ct where
  be y := ct.beLin y
  be_symm y a b := (ct.dat y).beta_symm a b
  be_bal y c c' h a b := PointLawsEdge.betaBal _ p _ _ (ct.dat y) c c' (h.trans (complexConj_eq_conj D _).symm) a b
  be_posDef y := PointLawsEdge.betaPosDef _ ct.hp.one_lt _ _ (ct.dat y)
  yl_rank y := by
    obtain ⟨ρ, h₁, h₂, h₃⟩ := PointLawsEdge.rank_le (ct.dat y)
    rw [finrank_host_eq, Nat.mul_div_cancel_left _ two_pos] at h₁
    have := S.p_eq
    have := S.rank_eq
    exact ⟨ρ, h₁, fun _ _ => by omega⟩
  psiV y a := vU p (ct.mulConst y a (w0 D • a))
  tau y := ct.tauVal y
  tau_add_left y a a' χ := (ct.evidence y).add_left a a' _
  tau_add_right y a χ χ' := (ct.evidence y).add_right a χ χ'
  tau_symm y a b := (ct.evidence y).symm a b
  tau_smul y c a χ := (ct.evidence y).bal c a χ
  be_tau y a b := (ct.evidence y).beta_eq a b
  multiplicationLatticeFirst y := ct.mulFst y
  multiplicationLatticeSecond y := ct.mulSnd y
  mulC y := ct.mulConst y
  psiV_def _ _ := rfl
  dimB y := ct.abDim y
  dimB_add y := ct.abDim_add y
  be_eq _ _ _ := rfl

section Api

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

theorem motTrue_mul (a b : ct.Ylat y) : (motTrue ct).multiplicationLatticeFirst y a b = ct.phi y b ∧ (motTrue ct).multiplicationLatticeSecond y a b = ct.phi y a ∧
    (motTrue ct).mulC y a b = (motTrue ct).tau y a (ct.phi y b) :=
  ⟨ct.mulFst_eq y a b, ct.mulSnd_eq y a b, ct.mulConst_eq y a b⟩

theorem motTrue_psiV_eq_be (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a (w0 D • a) := by
  rw [(motTrue ct).psiV_def, (motTrue_mul ct y _ _).2.2, (motTrue ct).be_tau]

theorem motTrue_psiV_half (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a a / 2 := by
  have h := (motTrue ct).be_bal y (w0 D) (1 - w0 D) (one_sub_halfSqrt_eq_conj D) a a
  rw [sub_smul, one_smul, map_sub, (motTrue ct).be_symm y (w0 D • a)] at h
  rw [motTrue_psiV_eq_be]
  linarith

end Api

end GlobalTheory.LocM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliary

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.LevelPlaceSep

theorem not_mem_two {D : D7} (P : PlE D.host) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : P ∈ placesOver D.host.E p) (h2 : P ∈ placesOver D.host.E q) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have e := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  push_cast at e
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  have h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h2
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')

theorem mem_placesOver_of_comap {D : D7} {P P' : PlE D.host}
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) {p : ℕ}
    (hP : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E)) := (map_natCast _ p).symm
  show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
  have hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hP
  rw [e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]
  exact hP'

theorem isConjPl_conjPlE {D : D7} (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj,
      GlobalTheory.FixedPlaceSplit.host_conj_conj]
  rw [this]

theorem eq_of_qpOf {D : D7} (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (S : Finset (PlE D.host)) {P P' : PlE D.host}
    (hP : P ∈ qpOf D Pq S) (hP' : P' ∈ qpOf D Pq S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) (hv' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) : P = P' := by
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e
  · exact e.symm
  have hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal := hPq v
  have hS : Pq v ∈ S := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'
    · rw [e']; exact qpOf_sub D Pq S hP
    · rw [e', ← e]; exact qpOf_sub D Pq S hP'
  exact (qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm

theorem g_ne_g {D : D7} {k k' : Fin 2} (h : k ≠ k') : D.host.g k ≠ D.host.g k' := by
  have h0 := D.host.g_ne
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

theorem levelPlaces_sep : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  intro D T i Q Pq sp hPq hQs hQ hpDs hsp
  obtain ⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧
      ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by
    refine ⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_,
      fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩
    · split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    · intro k
      split_ifs
      · exact (D.host.pde_ne_g k).2
      · exact (D.host.pde_ne_g k).1
  have hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := fun kv => D.naut.plGw_over kv.1 kv.2
  have c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i) := fun P hP hP' =>
    (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')
  have c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i) := fun kv =>
    ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv),
     fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩
  have c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    by_cases hk : k = k'
    · subst hk
      have : v = v' := D.naut.plGw_inj k h
      rw [this]
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (by rw [h]; exact hG ⟨k', v'⟩)).elim
  refine ⟨?_, c2, c3, c4⟩
  intro P P' hP hP' hv
  have hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P).w_under; rw [hsp P hP] at this; exact this
  have hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P').w_under; rw [hsp P' hP'] at this; rw [this, hv]
  have hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := hcP.trans hcP'.symm
  have same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc.symm h
  have same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc h
  rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩
  · exact eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'
  · exact ((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim
  · exact ((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim
  · exact eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'
  · exact (not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP))
      (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim
  · exact (not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP'))
      (same' (hG kv))).elim
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k = k'
    · subst hk
      rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e
      · exact e.symm
      · have hc2 := isConjPl_conjPlE (NX.pG D ⟨k, v⟩)
        rw [← e] at hc2
        exact (D.naut.plGw_nconj k v v' hc2).elim
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (same (hG ⟨k', v'⟩))).elim

end GlobalTheory.LevelPlaceSep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesAvoidAuxiliaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.split_places_avoid_auxiliary : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  first | exact @GlobalTheory.LevelPlaceSep.levelPlaces_sep | exact GlobalTheory.LevelPlaceSep.levelPlaces_sep | (intros; apply GlobalTheory.LevelPlaceSep.levelPlaces_sep <;> assumption)
end
end
