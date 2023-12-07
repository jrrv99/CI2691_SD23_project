import java.awt.Font;
import java.util.Scanner;

public class LineasRectangulosColores {
    /**
     * Panel
     */
    public static final int PANEL_BARRA_TITULO_ALTURA = 38; // alto de la barra de titulo 
    public static final int PANEL_DEFAULT_XMAX = 512;
    public static final int PANEL_DEFAULT_YMAX = 512;
    public static final String PANEL_DEFAULT_TITLE = "Lineas Rectangulos Colores";
    
    public static int PANEL_YMAX = PANEL_DEFAULT_YMAX;
    public static int PANEL_XMAX = PANEL_DEFAULT_XMAX;

    // Se suma el alto de la barra del titulo para normalizar el cuerpo del panel
    /**
     * Dado que cuando se abre, la ventana, el YMAX lo toma desde el inicio de la
     * ventana, no desde el punto (0,0), hay que sumarle la altura de la barra del
     * titulo al PANEL_YMAX para normalizar la altura del panel editable.
     */
    /*@ requires true;
      @ ensures \result == (PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA);
      @*/
    public static /*@ pure @*/ int normalizedPanelYMAX() {
        return PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA;
    }

    public static void main(String[] args) {
        MaquinaDeTrazados panel = new MaquinaDeTrazados(
            PANEL_XMAX,
            normalizedPanelYMAX(),
            PANEL_DEFAULT_TITLE,
            Colores.LIGHT_GRAY
        );
    }
}