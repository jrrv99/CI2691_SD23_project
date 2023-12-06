public class DibujosVarios {
    private static final double PROPORTION_PERCENTAGE = 0.7; // 70%

    public static /*@ pure @*/ void cuadricula(MaquinaDeTrazados plt) {
        plt.dibujarLinea(
            plt.XMAX / 3, 0,
            plt.XMAX / 3, plt.YMAX,
            Colores.WHITE);
        plt.dibujarLinea(
            2 * plt.XMAX / 3, 0,
            2 * plt.XMAX / 3, plt.YMAX,
            Colores.WHITE);
        plt.dibujarLinea(
            0, plt.YMAX / 3,
            plt.XMAX, plt.YMAX / 3,
            Colores.WHITE);
        plt.dibujarLinea(
            0, 2 * plt.YMAX / 3,
            plt.XMAX, 2 * plt.YMAX / 3,
            Colores.WHITE);

        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires 0 < r < Integer.MAX_VALUE;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarCirculo(MaquinaDeTrazados plt, int x, int y, int r) {
        plt.dibujarOvalo(x - r, y - r, 2*r, 2*r);
        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires 0 < r < Integer.MAX_VALUE;
	  @ requires color != null;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarCirculoLleno(MaquinaDeTrazados plt, int x, int y, int r, Colores color) {
        plt.dibujarOvaloLleno(x - r, y - r, 2*r, 2*r, color);
        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires 0 < l < Integer.MAX_VALUE;
	  @ requires color != null;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarCuadradoLleno(MaquinaDeTrazados plt, int x, int y, int l, Colores color) {
        plt.dibujarRectanguloLleno(x - (l / 2), y - (l / 2), l, l, color);
        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < b < Integer.MAX_VALUE;
	  @ requires 0 < h < Integer.MAX_VALUE;
	  @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarTriangulo(MaquinaDeTrazados plt, int b, int h, int x, int y) {
        int[] x_axis = new int[] {x, x + (b / 2), x - (b / 2)};
        int[] y_axis = new int[] {y - h, y, y};
        plt.dibujarPoligono​(x_axis, y_axis, 3);
        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < b < Integer.MAX_VALUE;
	  @ requires 0 < h < Integer.MAX_VALUE;
	  @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires color != null;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarTrianguloLleno(MaquinaDeTrazados plt, int b, int h, int x, int y, Colores color) {
        int[] x_axis = new int[] {x, x + (b / 2), x - (b / 2)};
        int[] y_axis = new int[] {y - h, y, y};
        plt.dibujarPoligono​Lleno(x_axis, y_axis, 3, color);
        plt.mostrar();
    }

    /*@ requires plt != null;
      @ requires 0 < plt.XMAX < Integer.MAX_VALUE;
      @ requires 0 < plt.YMAX < Integer.MAX_VALUE;
      @ requires x_axis.length == y_axis.length;
      @ requires (\forall int k; 0 <= k && k < x_axis.length; 0 <= x_axis[k]);
      @ requires (\forall int k; 0 <= k && k < y_axis.length; 0 <= y_axis[k]);
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarLineasConsecutivas(MaquinaDeTrazados plt, int[] x_axis, int[] y_axis) {
        int i = 1;

        /*@ maintaining 0 <= i <= x_axis.length;
          @ decreasing x_axis.length - i;
          @*/
        while(i < x_axis.length) {
            plt.dibujarLinea(x_axis[i-1], y_axis[i-1], x_axis[i], y_axis[i]);

            i++;
        }

        plt.mostrar();
    }

    /*@ requires plt != null;
      @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires l < Integer.MAX_VALUE;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarLineaHorizontal(MaquinaDeTrazados plt, int x, int y, int l) {
        plt.dibujarLinea(
            x, y,
            x + l, y
        );
        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 < plt.YMAX < Integer.MAX_VALUE;
      @*/
    public static /*@ pure @*/ void dibujarCaraSinExpresion(MaquinaDeTrazados plt) {
        int diameter = (int)((Math.min(plt.XMAX, plt.YMAX)) * PROPORTION_PERCENTAGE);
        int radius = (int)Math.round(diameter / 2);
        final int x_center = (int)(plt.XMAX/2);
        final int y_center = (int)(plt.YMAX/2);

        dibujarCirculoLleno(
            plt,
            x_center,
            y_center,
            radius,
            Colores.YELLOW);

        dibujarLineaHorizontal(
            plt,
            x_center - (3 * radius / 4),
            y_center - (radius / 4),
            radius / 2
        );

        dibujarLineaHorizontal(
            plt,
            x_center + (3 * radius / 4),
            y_center - (radius / 4),
            -(radius / 2)  // right to left
        );

        dibujarLineaHorizontal(
            plt,
            x_center - (radius / 2),
            y_center + (radius / 3),
            radius
        );

        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 < plt.YMAX < Integer.MAX_VALUE;
      @*/
    public static /*@ pure @*/ void dibujarCaraSinBoca(MaquinaDeTrazados plt) {
        int diameter = (int)((Math.min(plt.XMAX, plt.YMAX)) * PROPORTION_PERCENTAGE);
        int radius = (int)Math.round(diameter / 2);
        final int x_center = (int)(plt.XMAX/2);
        final int y_center = (int)(plt.YMAX/2);
        final int eyes_radius = (int)(radius / 6);
        final int eyes_y_coord = y_center - eyes_radius;

        dibujarCirculoLleno(
            plt,
            x_center,
            y_center,
            radius,
            Colores.YELLOW);


        dibujarCirculoLleno(plt, x_center - (diameter / 5), eyes_y_coord, eyes_radius, Colores.BLACK);
		dibujarCirculoLleno(plt, x_center + (diameter / 5), eyes_y_coord, eyes_radius, Colores.BLACK);

        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 < plt.YMAX < Integer.MAX_VALUE;
      @*/
    public static /*@ pure @*/ void dibujarCaraConOjosVolteados(MaquinaDeTrazados plt) {
        int diameter = (int)((Math.min(plt.XMAX, plt.YMAX)) * PROPORTION_PERCENTAGE);
        int radius = (int)Math.round(diameter / 2);
        final int x_center = (int)(plt.XMAX/2);
        final int y_center = (int)(plt.YMAX/2);
        final int eyes_radius = (int)(radius / 4);
        final int eyes_y_coord = y_center - 3 * eyes_radius / 4;
        final int eyes_ball_radius = (int)(radius / 12);
        final int eyes_ball_y_coord = eyes_y_coord - (eyes_radius - eyes_ball_radius);

        dibujarCirculoLleno(
            plt,
            x_center,
            y_center,
            radius,
            Colores.YELLOW
        );


        dibujarCirculoLleno(plt, x_center - (diameter / 5), eyes_y_coord, eyes_radius, Colores.WHITE);
		dibujarCirculoLleno(plt, x_center + (diameter / 5), eyes_y_coord, eyes_radius, Colores.WHITE);
        dibujarCirculoLleno(plt, x_center - (diameter / 5), eyes_ball_y_coord, eyes_ball_radius, Colores.BLACK);
		dibujarCirculoLleno(plt, x_center + (diameter / 5), eyes_ball_y_coord, eyes_ball_radius, Colores.BLACK);

        dibujarCirculoLleno(
            plt,
            x_center - (3 * radius / 8) + eyes_ball_radius,
            y_center + (radius / 3) + eyes_ball_radius,
            eyes_ball_radius,
            Colores.BLACK);

		dibujarCirculoLleno(
            plt,
            x_center + (3 * radius / 8) - eyes_ball_radius,
            y_center + (radius / 3) + eyes_ball_radius,
            eyes_ball_radius,
            Colores.BLACK);

        plt.dibujarRectanguloLleno(
            x_center - (3 * radius / 8) + eyes_ball_radius,
            y_center + (radius / 3),
            (3 * radius / 4) - 2 * eyes_ball_radius,  // width: 
            eyes_ball_radius * 2  // height: eyes_ball_diameter
        );

        plt.mostrar();
    }

    /*@ requires plt != null;
	  @ requires 0 < plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 < plt.YMAX < Integer.MAX_VALUE;
      @*/
    public static /*@ pure @*/ void dibujarRobot(MaquinaDeTrazados plt) {
        int side = (int)((Math.min(plt.XMAX, plt.YMAX)) * PROPORTION_PERCENTAGE);
        int i = 0;
        int x_center = (int)Math.round(plt.XMAX / 2);
        int y_center = (int)Math.round(plt.YMAX / 2);

        int eyes_radius = side / 8;
        int eyes_border_radius = (int)Math.round(eyes_radius * 1.1);
        int eyes_y_coord = (int)Math.round(y_center - 3 * eyes_radius / 2);
        int mouth_radius = (int)Math.round(side / 12);
        int teeth_width = (int)Math.round((Math.round(side / 2) - mouth_radius) / 9);
        int antenna_inner_radius = (int)Math.round(eyes_radius * 0.2);
        int antenna_outter_radius = (int)Math.round(eyes_radius * 0.4);
        int antenna_y_coord = (int)Math.round(y_center - (side / 2) - (mouth_radius * 1.5));

        /* Antenna */
        dibujarCirculoLleno(
            plt,
            x_center,
            antenna_y_coord,
            antenna_outter_radius,
            Colores.LIGHT_GRAY);

        dibujarCirculoLleno(
            plt,
            x_center,
            antenna_y_coord,
            antenna_inner_radius,
            Colores.RED);
        
        plt.dibujarRectanguloLleno(
            x_center - antenna_inner_radius,
            antenna_y_coord + antenna_inner_radius,
            antenna_inner_radius * 2,
            y_center- side/2 - antenna_y_coord,
            Colores.LIGHT_GRAY
        );

        /* Left ear */
        // Left ear top circle 
        dibujarCirculoLleno(
            plt,
            x_center - side/2,
            y_center - (side/2 - mouth_radius) / 2,
            mouth_radius,
            Colores.RED);

        // Left ear bottom circle
		dibujarCirculoLleno(
            plt,
            x_center - side/2,
            y_center + (side/2 - mouth_radius) / 2,
            mouth_radius,
            Colores.RED);

        // Left ear body
        plt.dibujarRectanguloLleno(
            x_center - side/2 - mouth_radius,
            y_center - (side/2 - mouth_radius) / 2,
            mouth_radius * 2,  // width: 
            side/2 - mouth_radius,  // height: eyes_ball_diameter,
            Colores.RED);

        /* Right ear */
        // Right ear top circle 
        dibujarCirculoLleno(
            plt,
            x_center + side/2,
            y_center - (side/2 - mouth_radius) / 2,
            mouth_radius,
            Colores.RED);

        // Right ear bottom circle
		dibujarCirculoLleno(
            plt,
            x_center + side/2,
            y_center + (side/2 - mouth_radius) / 2,
            mouth_radius,
            Colores.RED);

        // Right ear body
        plt.dibujarRectanguloLleno(
            x_center + side/2 - mouth_radius,
            y_center - (side/2 - mouth_radius) / 2,
            mouth_radius * 2,  // width: 
            side/2 - mouth_radius,  // height: eyes_ball_diameter,
            Colores.RED);

        /* Fase */
        dibujarCuadradoLleno(plt, x_center, y_center, side, Colores.LIGHT_GRAY);

        /* Left eye */
        dibujarCirculoLleno(plt, x_center - (side / 4), eyes_y_coord, eyes_border_radius, Colores.BLACK);
        dibujarCirculoLleno(plt, x_center - (side / 4), eyes_y_coord, eyes_radius, Colores.WHITE);

        /* Right eye */
		dibujarCirculoLleno(plt, x_center + (side / 4), eyes_y_coord, eyes_border_radius, Colores.BLACK);
		dibujarCirculoLleno(plt, x_center + (side / 4), eyes_y_coord, eyes_radius, Colores.WHITE);

        /* Nose */
        dibujarTrianguloLleno(plt, 2*eyes_radius, 3*eyes_radius/2, x_center, y_center + eyes_radius / 2, Colores.RED);

        /* Mouth */
        // mouth left circle 
        dibujarCirculoLleno(
            plt,
            x_center - side / 4 + mouth_radius / 2,
            y_center + ((side / 2) / 3) + mouth_radius,
            mouth_radius,
            Colores.WHITE);
        // mouth right circle
		dibujarCirculoLleno(
            plt,
            x_center + side / 4 - mouth_radius / 2,
            y_center + ((side / 2) / 3) + mouth_radius,
            mouth_radius,
            Colores.WHITE);

        // mouth body
        plt.dibujarRectanguloLleno(
            x_center - side / 4 + mouth_radius / 2,
            y_center + ((side /  2) / 3),
            side / 2 - mouth_radius,  // width: 
            mouth_radius * 2,  // height: eyes_ball_diameter,
            Colores.WHITE
        );

        // teeth
        while (i <= 4){
            plt.dibujarRectanguloLleno(
                x_center - Math.round(side / 4) + Math.round(mouth_radius / 2) + (teeth_width * 2 * i) + 2*i,
                y_center + ((side/2) / 3),
                teeth_width,  // width: 
                mouth_radius * 2  // height: eyes_ball_diameter,
            );

            i++;
        }

        plt.mostrar();
    }
}
