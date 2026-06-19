import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericMatrixClauses
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexAnchorCertificateTopology
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericPolynomialCover

set_option autoImplicit false

open MeasureTheory

namespace TransformerIdentifiability.NLayer

/-!
# Concrete exact TeX genericity wrappers

This file integrates the three focused genericity shards:

* `(G1)`--`(G3)` matrix-clause topology;
* `(G4)` anchor-certificate topology;
* positive-dimensional polynomial covers for the exact bad set.
-/

/-- Concrete topology obligations for the explicit matrix clauses `(G1)`--`(G3)`. -/
theorem texGenericMatrixClauseTopologyObligations :
    TexGenericMatrixClauseTopologyObligations :=
  texGenericMatrixClauseTopologyObligations_concrete

/-- Concrete topology obligations for the exact anchor certificate `(G4)`. -/
theorem texAnchorCertificateTopologyObligations :
    TexAnchorCertificateTopologyObligations :=
  { isOpen := texAnchorCertificateRowBoundTopologyObligations_concrete.isOpen
    dense := texAnchorCertificateRowBoundTopologyObligations_concrete.dense }

/-- The exact TeX generic set is open. -/
theorem isOpen_TexGenericSet (L d : Nat) : IsOpen (TexGenericSet L d) :=
  isOpen_TexGenericSet_of_texAnchorCertificate_open_dense
    texGenericMatrixClauseTopologyObligations
    texAnchorCertificateTopologyObligations L d

/-- The exact TeX generic set is dense in positive dimension and under the
certificate-row dimension bound. -/
theorem dense_TexGenericSet
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Dense (TexGenericSet L d) :=
  dense_TexGenericSet_of_texAnchorCertificate_open_dense
    texGenericMatrixClauseTopologyObligations texAnchorCertificateTopologyObligations
    L d hd hrows

/-- Concrete polynomial cover for the exact TeX generic set under the certificate-row
dimension bound. -/
theorem texGenericBadSet_exists_polynomialNonvanishingCover
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Nonempty (TexGenericPolynomialNonvanishingCover L d) :=
  texGenericBadSet_exists_polynomialNonvanishingCover_concrete_of_pos_d L d hd hrows

/-- A chosen algebraic cover witness under the certificate-row dimension bound. -/
noncomputable def texGenericBadSet_polynomialNonvanishingCover
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    TexGenericPolynomialNonvanishingCover L d :=
  Classical.choice (texGenericBadSet_exists_polynomialNonvanishingCover L d hd hrows)

/-- Exact TeX generic bad-set nullness under the certificate-row dimension bound. -/
theorem texGenericBadSet_null
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    volume (TexGenericBadSet L d : Set (Params L d)) = 0 :=
  texGenericBadSet_null_of_polynomialNonvanishingCover
    (texGenericBadSet_polynomialNonvanishingCover L d hd hrows)

end TransformerIdentifiability.NLayer
