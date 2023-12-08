import java.util.Random;
import java.awt.Font;

public class Utils {
    //Retorna el numero divisible por M mas cercano a N
    /*@ requires 0 < N <= Integer.MAX_VALUE;
      @ requires 0 < M <=  Integer.MAX_VALUE;
      @ requires M <= N;
      @*/
    public static /*@ pure @*/ int NormalizeToExactlyDivisible(int N, int M) {
        int divisible = (int)Math.round(N / M) * M;
        return divisible;
    }

    /*@ requires plt != null;
      @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires l < Integer.MAX_VALUE;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarLineaHorizontal(MaquinaDeTrazados plt, int x, int y, int l, Colores color) {
        plt.dibujarLinea(
            x, y,
            x + l, y,
            color
        );
        plt.mostrar();
    }

    /*@ requires plt != null;
      @ requires 0 <= x <= plt.XMAX < Integer.MAX_VALUE;
	  @ requires 0 <= y <= plt.YMAX < Integer.MAX_VALUE;
	  @ requires l < Integer.MAX_VALUE;
      @ ensures true;
      @*/
    public static /*@ pure @*/ void dibujarLineaVertical(MaquinaDeTrazados plt, int x, int y, int l, Colores color) {
        plt.dibujarLinea(
            x, y,
            x, y + l,
            color
        );
        plt.mostrar();
    }

    public static /*@ pure @*/ void dibujarReglasDeCuadricula(MaquinaDeTrazados plt, int x, int y, int size, int SLOTS_NUMBER) {
        int i = 0;
        int NORMALIZED_SIZE = NormalizeToExactlyDivisible(size, SLOTS_NUMBER);
        int LINE_WIDTH = 1;
        int SLOT_WIDTH = NORMALIZED_SIZE / SLOTS_NUMBER;

		while(i < SLOTS_NUMBER) {
            dibujarLineaHorizontal(plt, x - SLOT_WIDTH / 2, y + SLOT_WIDTH * i + SLOT_WIDTH / 2, NORMALIZED_SIZE + SLOT_WIDTH, Colores.RED);
            dibujarLineaVertical(plt, x + SLOT_WIDTH * i + SLOT_WIDTH / 2, y - SLOT_WIDTH / 2, NORMALIZED_SIZE + SLOT_WIDTH, Colores.RED);
            i++;
		}
	}

    public static /*@ pure @*/ void dibujarIndices(MaquinaDeTrazados plt, int x, int y, int size, int SLOTS_NUMBER) {
        int i = 0;
        int NORMALIZED_SIZE = NormalizeToExactlyDivisible(size, SLOTS_NUMBER);
        int LINE_WIDTH = 1;
        int SLOT_WIDTH = NORMALIZED_SIZE / SLOTS_NUMBER;

        plt.configurarFuente("SansSerif", Font.PLAIN, 12);

		while(i < SLOTS_NUMBER) {
            // Numero horizontal del slot
            plt.dibujarString(Integer.toString(i), x + SLOT_WIDTH * i + (SLOT_WIDTH / 2) - 4, y - (SLOT_WIDTH / 2) + 5);
            
            // Pintar numero vertical
            plt.dibujarString(Integer.toString(i), x - (SLOT_WIDTH / 2), y + SLOT_WIDTH * i + (SLOT_WIDTH / 2) + 5);
		}
	}

	public static /*@ pure @*/ void printGrid(MaquinaDeTrazados plt, int x, int y, int size, int SLOTS_NUMBER) {
        int i = 0;
        int NORMALIZED_SIZE = NormalizeToExactlyDivisible(size, SLOTS_NUMBER);
        int LINE_WIDTH = 1;
        int SLOT_WIDTH = NORMALIZED_SIZE / SLOTS_NUMBER;

		while(i < SLOTS_NUMBER + 1) {
            // Linea Horizontal del grid
			dibujarLineaHorizontal(plt, x, y + SLOT_WIDTH * i, NORMALIZED_SIZE, Colores.BLACK);
            // Linea Vertical del grid
			dibujarLineaVertical(plt, x + SLOT_WIDTH * i, y, NORMALIZED_SIZE, Colores.BLACK);
            i++;
		}
	}

    public static void imprimirTableroPorConsola(int[][] tablero, int size) {
        int fila = 0, columna;

        while (fila < size) {
            columna = 0;
            System.out.print("| ");
            while (columna < size) {
                System.out.print(
                (tablero[fila][columna] != -1 ? tablero[fila][columna] : " ")
                + (columna < size - 1 ? " | " : " |\n"));
                columna++;
            }
            fila++;
        }
    }

    public static void cleanConsole(String... arg) {
        System.out.print("\033[H\033[2J");  
        System.out.flush();  
    }
} 