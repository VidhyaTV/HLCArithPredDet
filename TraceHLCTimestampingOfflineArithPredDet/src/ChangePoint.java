class ChangePoint
{
    Clock cPointTimestamp;
    int endpointType;//+1 for left endpoint, -1 for right endpoint
    int iValue;
    ChangePoint(Clock cPtTimestamp, int ePoint, int value)
    {
        cPointTimestamp=cPtTimestamp;
        endpointType=ePoint;
        iValue = value;
    }
    Clock getcPointTimestamp()
    {
        return cPointTimestamp;
    }
    int getEndPointType()
    {
        return endpointType;
    }
    int getiValue()
    {
        return iValue;
    }
    void setcPointTimestamp(Clock cPtTimestamp)
    {
        cPointTimestamp=cPtTimestamp;
    }
    void setEndPointType(int ePoint)
    {
        endpointType=ePoint;
    }
    void setiValue(int value){iValue = value;}
}