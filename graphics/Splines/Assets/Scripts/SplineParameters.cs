/*  CSCI-B581 / Spring 2021 / Mitja Hmeljak
    Assignment 02 starting C# program code
    This script should:
    provide the correct parameters in the spline matrices,
    as from the matrix form,
    defined as in Textbook Chapter 17.1.1.
                         
    However, keep in mind that Unity Matrix4x4 are "column major",
    as detailed in assignment instructions.
    Original demo code by CSCI-B481 alumnus Rajin Shankar, IU Computer Science.
 */

using UnityEngine;


namespace A03 {

    public static class SplineParameters    {
    
        public enum SplineType { Bezier, CatmullRom, Bspline }

        public static Matrix4x4 GetMatrix(SplineType type) {
        
            switch (type) {
                // TODO: generate Bezier spline matrix,
                //   with constants defined as in Textbook Chapter 17.1.1, equation 17.9
                case SplineType.Bezier:
                    return new Matrix4x4( // COLUMN MAJOR!
                        new Vector4(-1, 3, -3, 1),
                        new Vector4(3, -6, 3, 0),
                        new Vector4(-3, 3, 0, 0),
                        new Vector4(1, 0, 0, 0)
                    );
                // TODO: generate Catmull-Rom spline matrix,
                //   with constants as per Lecture 11 :
                case SplineType.CatmullRom:
                    return new Matrix4x4( // COLUMN MAJOR!
                        new Vector4(-1, 3, -3, 1) * 1/2,
                        new Vector4(2, -5, 4, -1) * 1/2,
                        new Vector4(-1, 0, 1, 0) * 1/2,
                        new Vector4(0, 2, 0, 0) * 1/2
                    );
                // TODO: generate B-spline matrix,
                //   with constants as per Lecture 11 :
                case SplineType.Bspline:
                    return new Matrix4x4( // COLUMN MAJOR!
                        new Vector4(-1, 3, -3, 1) * 1/6,
                        new Vector4(3, -6, 3, 0) * 1/6,
                        new Vector4(-3, 0, 3, 0) * 1/6,
                        new Vector4(1, 4, 1, 0) * 1/6
                    );
                default:
                    return Matrix4x4.identity;
            }
        } // end of GetMatrix()

        // this could be useful for multi-segment spline curves:
        public static bool UsesConnectedEndpoints(SplineType type) {
            switch (type) {
                case SplineType.Bezier: return true;
                case SplineType.CatmullRom: return false;
                case SplineType.Bspline: return false;
                default: return false;
            }
        } // end of UsesConnectedEndpoints()
        
    } // end of class SplineParameters
    
} // end of namespace A03
