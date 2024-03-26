/*  CSCI-B581 / Spring 2021 / Mitja Hmeljak

    The Vertex Shader component in this Unity Shader should:

    use t1, t2 values to compute the position of each 
       vertex on the Spline Curve:
    t1 is for the "base curve",
    t2 is for the "offset curve".

    to calculate (on the GPU) the vertices on a single Spline Curve segment,
    to be displayed as a Mesh, using a Mesh Renderer.

    Original demo code by CSCI-B481 alumnus Rajin Shankar, IU Computer Science.
 */




Shader "SplineVertexShader" {

    Properties { }
    
    SubShader {
    
        cull off
        
        Tags { "RenderType"="Opaque" "Queue"="Transparent" }
        
        Pass  {
        
            CGPROGRAM
            
            // we'll provide both Vertex and Fragment shaders:
            #pragma vertex vert
            #pragma fragment frag
            
            #include "UnityCG.cginc"

            struct appdata {
                float4 vertex : POSITION;
            };

            // "varying" struct of variables,
            //     passed from vertex shader
            //     to fragment shader:
            struct v2f {
                float4 vertex : SV_POSITION;
            };
            
            // here we receive (from application, CPU side) the spline Hermite form matrix:
            float4x4 _SplineMatrix;
            
            // here we receive (from application, CPU side) the four control points:
            float2 _Control0, _Control1, _Control2, _Control3;
            
            // here we receive (from application, CPU side) how many steps there should be on curve:
            float _Step;
            
            

            // ---------------------------------------------------------
            // the main spline calculation happens here, i.e.
            // you need to compute the spline multiplication as from the matrix form
            //  (defined as in Textbook Chapter 17.1.1,
            //   for example equation 17.9 for Bezier curves)
            // i.e.
            // in the form p(t) = t * M * p
            //   
            //   Note: matrices are defined in "column major" !
            //
            float4 HermiteMult(float4x4 controlP, float4x4 splineM, float4 tParamsVector) {
                // TODO - compute vertex on curve:
                float4x4 composedM = mul(controlP, splineM);
                float4 vertexOnCurve = mul(composedM, tParamsVector);
                return vertexOnCurve;
            } // end of HermiteMult()



            // ---------------------------------------------------------
            // compute the Normal to the curve, at vertex provided by parameter t:
            // 
            float2 GetNormalToCurve(float t, float dt, float4x4 controlMatrix, float4x4 splineMatrix) {
                //
                // TODO - compute normal to segment (p1, p2) on curve
                //        where p1 is the vertex on curve at parameter t
                //        where p2 is the vertex on curve at parameter t2 = t + dt
                //
                // ADDITIONAL NOTE:
                //      The resulting normal should be normalized before returning it!
                //      And the returned value should be a float2 (not a float4!)
                //
                // get t2
                float t2 = t + dt;
                // build tRow of t & t2
                float4 tRow1 = float4(t*t*t, t*t, t, 1);
                float4 tRow2 = float4(t2*t2*t2, t2*t2, t2, 1);
                // compute world position of p1 & p2
                float4 worldPosition1 = HermiteMult(controlMatrix, splineMatrix, tRow1);
                float4 worldPosition2 = HermiteMult(controlMatrix, splineMatrix, tRow2);
                float2 p1 = float2(worldPosition1.x, worldPosition1.y);
                float2 p2 = float2(worldPosition2.x, worldPosition2.y);
                // compute normal
                float2 d = p2 - p1; // direction vector
                float l = sqrt(d.x*d.x + d.y*d.y); // length of direction vector
                float2 normal = float2(-d.y/l, d.x/l);
                return normal;
            }  // end of GetNormalToCurve()
            


            // ---------------------------------------------------------
            // the Vertex Shaders outputs positions on the Spline Curve:
            v2f vert (appdata v) {
            
                // the output to this shader is:
                v2f o;
                
                // in the vertex shader,
                //  we receive t in the x parameter,
                //  and the offset in the y parameter:
                float t = v.vertex.x;
                float offset = v.vertex.y;
                float4 tRow = float4(t*t*t, t*t, t, 1);

                //
                // TODO - compute matrix of four Control Points for spline:
                //
                float4x4 controlMatrix = float4x4(
                    _Control0.x, _Control1.x, _Control2.x, _Control3.x,
                    _Control0.y, _Control1.y, _Control2.y, _Control3.y,
                    0, 0, 0, 0,
                    1, 1, 1, 1
                );

                // base spline:
                float4 worldPosition = HermiteMult(controlMatrix, _SplineMatrix, tRow);

                // normal to obtain point on offset curve:
                float2 normal = GetNormalToCurve(t, _Step, controlMatrix, _SplineMatrix);

                // the following will do nothing when offset is 0,
                //         i.e. vertex on "base curve",
                // but it will move the vertex in the direction of the normal
                //         for the vertex on "offset curve":
                worldPosition.xy -= normal * offset;

                worldPosition.z = 0;
                worldPosition.w = 1;

                o.vertex = mul(UNITY_MATRIX_VP, worldPosition);

                return o;
            } // end of vert shader


            // -------------------------------------------------
            // the Fragment Shader simply outputs a fixed color:

            fixed4 _Color;

            fixed4 frag (v2f i) : SV_Target {
                return _Color;
            } // end of frag shader

            ENDCG
        }
    }
}